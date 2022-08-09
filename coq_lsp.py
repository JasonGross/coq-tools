from collections import defaultdict
import tempfile
import atexit
import contextlib
import functools
import pprint
import pathlib
import shutil
import subprocess
import sys
import textwrap
import re
import threading
import queue
import time

import pytest

import sansio_lsp_client as lsp


METHOD_COMPLETION = "completion"
METHOD_HOVER = "hover"
METHOD_SIG_HELP = "signatureHelp"
METHOD_DEFINITION = "definition"
METHOD_REFERENCES = "references"
METHOD_IMPLEMENTATION = "implementation"
METHOD_DECLARATION = "declaration"
METHOD_TYPEDEF = "typeDefinition"
METHOD_DOC_SYMBOLS = "documentSymbol"
METHOD_FORMAT_DOC = "formatting"
METHOD_FORMAT_SEL = "rangeFormatting"

RESPONSE_TYPES = {
    METHOD_COMPLETION: lsp.Completion,
    METHOD_HOVER: lsp.Hover,
    METHOD_SIG_HELP: lsp.SignatureHelp,
    METHOD_DEFINITION: lsp.Definition,
    METHOD_REFERENCES: lsp.References,
    METHOD_IMPLEMENTATION: lsp.Implementation,
    METHOD_DECLARATION: lsp.Declaration,
    METHOD_TYPEDEF: lsp.TypeDefinition,
    METHOD_DOC_SYMBOLS: lsp.MDocumentSymbols,
    METHOD_FORMAT_DOC: lsp.DocumentFormatting,
    METHOD_FORMAT_SEL: lsp.DocumentFormatting,
}


def find_method_marker(text, method):
    """ searches for line: `<code> #<method>-<shift>`
          - example: `sys.getdefaultencoding() #{METHOD_COMPLETION}-5`
            position returned will be 5 chars before `#...`: `sys.getdefaultencodi | ng()`
    """
    match = re.search(rf"\#{method}-(\d+)", text)
    before_match = text[: match.start()]
    lineno = before_match.count("\n")
    column = len(before_match.split("\n")[-1]) - int(match.group(1))
    return lsp.Position(line=lineno, character=column)


class ThreadedServer:
    """
    Gathers all messages received from server - to handle random-order-messages
    that are not a response to a request.
    """

    def __init__(self, process, root_uri):
        self.process = process
        self.root_uri = root_uri
        self.lsp_client = lsp.Client(
            root_uri=root_uri,
            workspace_folders=[lsp.WorkspaceFolder(uri=self.root_uri, name="Root")],
            trace="verbose",
        )
        self.msgs = []

        self._pout = process.stdout
        self._pin = process.stdin

        self._read_q = queue.Queue()
        self._send_q = queue.Queue()

        self.reader_thread = threading.Thread(
            target=self._read_loop, name="lsp-reader", daemon=True
        )
        self.writer_thread = threading.Thread(
            target=self._send_loop, name="lsp-writer", daemon=True
        )

        self.reader_thread.start()
        self.writer_thread.start()

        self.exception = None

    # threaded
    def _read_loop(self):
        try:
            while True:
                data = self.process.stdout.read(1)

                if data == b"":
                    break

                self._read_q.put(data)
        except Exception as ex:
            self.exception = ex
        self._send_q.put_nowait(None)  # stop send loop

    # threaded
    def _send_loop(self):
        try:
            while True:
                chunk = self._send_q.get()
                if chunk is None:
                    break

                # print(f"\nsending: {buf}\n")
                self.process.stdin.write(chunk)
                self.process.stdin.flush()
        except Exception as ex:
            self.exception = ex

    def _queue_data_to_send(self):
        send_buf = self.lsp_client.send()
        if send_buf:
            self._send_q.put(send_buf)

    def _read_data_received(self):
        while not self._read_q.empty():
            data = self._read_q.get()
            events = self.lsp_client.recv(data)
            for ev in events:
                self.msgs.append(ev)
                self._try_default_reply(ev)

    def _try_default_reply(self, msg):
        if isinstance(
            msg,
            (
                lsp.ShowMessageRequest,
                lsp.WorkDoneProgressCreate,
                lsp.RegisterCapabilityRequest,
                lsp.ConfigurationRequest,
            ),
        ):
            msg.reply()

        elif isinstance(msg, lsp.WorkspaceFolders):
            msg.reply([lsp.WorkspaceFolder(uri=self.root_uri, name="Root")])

    #        else:
    #            print(f"Can't autoreply: {type(msg)}")

    def wait_for_message_of_type(self, type_, timeout=5):
        end_time = time.monotonic() + timeout
        while time.monotonic() < end_time:
            self._queue_data_to_send()
            self._read_data_received()

            # raise thread's exception if have any
            if self.exception:
                raise self.exception

            for msg in self.msgs:
                if isinstance(msg, type_):
                    self.msgs.remove(msg)
                    return msg

            time.sleep(0.2)

        raise Exception(
            f"Didn't receive {type_} in time; have: " + pprint.pformat(self.msgs)
        )

    def exit_cleanly(self):
        # Not necessarily error, gopls sends logging messages for example
        #        if self.msgs:
        #            print(
        #                "* unprocessed messages: " + pprint.pformat(self.msgs)
        #            )

        assert self.lsp_client.state == lsp.ClientState.NORMAL
        self.lsp_client.shutdown()
        self.wait_for_message_of_type(lsp.Shutdown)
        self.lsp_client.exit()
        self._queue_data_to_send()
        self._read_data_received()

    def do_method(self, text, file_uri, method, response_type=None):
        def doc_pos():
            return lsp.TextDocumentPosition(
                textDocument=lsp.TextDocumentIdentifier(uri=file_uri),
                position=find_method_marker(text, method),
            )

        if not response_type:
            response_type = RESPONSE_TYPES[method]

        if method == METHOD_COMPLETION:
            event_id = self.lsp_client.completion(
                text_document_position=doc_pos(),
                context=lsp.CompletionContext(
                    triggerKind=lsp.CompletionTriggerKind.INVOKED
                ),
            )
        elif method == METHOD_HOVER:
            event_id = self.lsp_client.hover(text_document_position=doc_pos())
        elif method == METHOD_SIG_HELP:
            event_id = self.lsp_client.signatureHelp(text_document_position=doc_pos())
        elif method == METHOD_DEFINITION:
            event_id = self.lsp_client.definition(text_document_position=doc_pos())
        elif method == METHOD_REFERENCES:
            event_id = self.lsp_client.references(text_document_position=doc_pos())
        elif method == METHOD_IMPLEMENTATION:
            event_id = self.lsp_client.implementation(text_document_position=doc_pos())
        elif method == METHOD_DECLARATION:
            event_id = self.lsp_client.declaration(text_document_position=doc_pos())
        elif method == METHOD_TYPEDEF:
            event_id = self.lsp_client.typeDefinition(text_document_position=doc_pos())
        elif method == METHOD_DOC_SYMBOLS:
            _docid = lsp.TextDocumentIdentifier(uri=file_uri)
            event_id = self.lsp_client.documentSymbol(text_document=_docid)
        else:
            raise NotImplementedError(method)

        resp = self.wait_for_message_of_type(response_type)
        assert not hasattr(resp, "message_id") or resp.message_id == event_id
        return resp


SERVER_COMMANDS = {
    "coq-lsp": ["/home/egallego/research/coq-lsp/_build/install/default/bin/coq-lsp"],
}

@contextlib.contextmanager
def start_server(langserver_name, project_root, file_contents):
    command = SERVER_COMMANDS[langserver_name]

    # Create files before langserver starts
    for fn, text in file_contents.items():
        path = project_root / fn
        path.write_text(text)

    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    tserver = ThreadedServer(process, project_root.as_uri())

    try:
        yield (tserver, project_root)
    except Exception as e:
        # Prevent freezing tests
        process.kill()
        raise e

    tserver.exit_cleanly()

def check_that_langserver_works(langserver_name, tmp_path):
    if langserver_name == "coq-lsp":
        file_contents = {
            "foo.v": textwrap.dedent(
                f"""\
                Definition a := 3.
                Lemma foo : True. Proof. auto. Qed."""
            )
        }
        filename = "foo.v"
        language_id = "coq"

    else:
        raise ValueError(langserver_name)

    with start_server(langserver_name, tmp_path, file_contents) as (
        tserver,
        project_root,
    ):
        # Initialized #####
        tserver.wait_for_message_of_type(lsp.Initialized)
        tserver.lsp_client.did_open(
            lsp.TextDocumentItem(
                uri=(project_root / filename).as_uri(),
                languageId=language_id,
                text=file_contents[filename],
                version=0,
            )
        )

        # Diagnostics #####
        diagnostics = tserver.wait_for_message_of_type(lsp.PublishDiagnostics)
        assert diagnostics.uri == (project_root / filename).as_uri()
        diag_msgs = [diag.message for diag in diagnostics.diagnostics]

        if langserver_name == "coq-lsp":
            print(diag_msgs)
        else:
            raise ValueError(langserver_name)

        file_contents = {
            "foo.v": textwrap.dedent(
                f"""\
                Definition a := 3.
                Lemma foo : True. Proof. auto. Qed.

                Lemma bar : False. Admitted."""
            )
        }

        tserver.lsp_client.did_change(
           lsp.TextDocumentItem(
                uri=(project_root / filename).as_uri(),
                languageId=language_id,
                text=file_contents[filename],
                version=1,
           ),
           [lsp.TextDocumentContentChangeEvent.whole_document_change(file_contents[filename])]
        )
        # Diagnostics #####
        diagnostics = tserver.wait_for_message_of_type(lsp.PublishDiagnostics)
        assert diagnostics.uri == (project_root / filename).as_uri()
        diag_msgs = [diag.message for diag in diagnostics.diagnostics]

        if langserver_name == "coq-lsp":
            print(diag_msgs)
        else:
            raise ValueError(langserver_name)

__all__ = ["get_coq_output"]

class defaultkeyeddict(defaultdict):
    def __missing__(self, key):
        self.__setitem__(key, self.default_factory(key))
        return self.__getitem__(key)

def initialize_lsp_server(coq_lsp, project_root=None):
    cleaners = []
    refs = []
    if project_root is None:
        project_dir_object = tempfile.TemporaryDirectory()
        project_root = pathlib.Path(project_dir_object.name)
        cleaners.append((project_dir_object.cleanup, [], {}))
        refs.append(project_dir_object)

    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    tserver = ThreadedServer(process, project_root.as_uri())

    cleaners.append((tserver.exit_cleanly, [], {}))

    return {'timeout': None,
            'cleaners': cleaners,
            'process': process,
            'server': tserver,
            'refs': refs,
            'project_root': project_root,
            'initialized': False}

COQ_LSP_SERVERS = defaultkeyeddict(initialize_lsp_server)

def get_timeout(coq_lsp=None):
    return COQ_LSP_SERVERS[coq_lsp].get('timeout')

def set_timeout(key, value, **kwargs):
    kwargs['log']('\nThe timeout for %s has been set to: %d' % (key, value))
    COQ_LSP_SERVERS[key]['timeout'] = value

def reset_timeout(*coq_lsps):
    if len(coq_lsps) == 0: coq_lsps = COQ_LSP_SERVERS.keys()
    for coq_lsp in coq_lsps:
        COQ_LSP_SERVERS[coq_lsp]['timeout'] = None
        # TODO: reset the internal timeout on the lsp server

def finalize_coq_lsp_servers(*coq_lsps):
    if len(coq_lsps) == 0: coq_lsps = COQ_LSP_SERVERS.keys()
    for coq_lsp in coq_lsps:
        for cleaner, args, kwargs in COQ_LSP_SERVERS[coq_lsp]['cleaners']:
            cleaner(*args, **kwargs)
        del COQ_LSP_SERVERS[coq_lsp]

atexit.register(finalize_coq_lsp_servers)

def
tserver.wait_for_message_of_type(lsp.Initialized)
def


@contextlib.contextmanager
def start_server(command, project_root, file_contents):
    # Create files before langserver starts
    for fn, text in file_contents.items():
        path = project_root / fn
        path.write_text(text)

    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    tserver = ThreadedServer(process, project_root.as_uri())

    try:
        yield (tserver, project_root)
    except Exception as e:
        # Prevent freezing tests
        process.kill()
        raise e

    tserver.exit_cleanly()

def get_lsp_


def start_server(langserver_name, project_root, file_contents):
    command = SERVER_COMMANDS[langserver_name]

    # Create files before langserver starts
    for fn, text in file_contents.items():
        path = project_root / fn
        path.write_text(text)

    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    tserver = ThreadedServer(process, project_root.as_uri())

    try:
        yield (tserver, project_root)
    except Exception as e:
        # Prevent freezing tests
        process.kill()
        raise e

    tserver.exit_cleanly()

    if
    with start_server(langserver_name, tmp_path, file_contents) as (
        tserver,
        project_root,
    ):

    if langserver_name == "coq-lsp":
        file_contents = {
            "foo.v": textwrap.dedent(
                f"""\
                Definition a := 3.
                Lemma foo : True. Proof. auto. Qed."""
            )
        }
        filename = "foo.v"
        language_id = "coq"

    else:
        raise ValueError(langserver_name)

    with start_server(langserver_name, tmp_path, file_contents) as (
        tserver,
        project_root,
    ):
        # Initialized #####
        tserver.wait_for_message_of_type(lsp.Initialized)
        tserver.lsp_client.did_open(
            lsp.TextDocumentItem(
                uri=(project_root / filename).as_uri(),
                languageId=language_id,
                text=file_contents[filename],
                version=0,
            )
        )

        # Diagnostics #####
        diagnostics = tserver.wait_for_message_of_type(lsp.PublishDiagnostics)
        assert diagnostics.uri == (project_root / filename).as_uri()
        diag_msgs = [diag.message for diag in diagnostics.diagnostics]

        if langserver_name == "coq-lsp":
            print(diag_msgs)
        else:
            raise ValueError(langserver_name)

        file_contents = {
            "foo.v": textwrap.dedent(
                f"""\
                Definition a := 3.
                Lemma foo : True. Proof. auto. Qed.

                Lemma bar : False. Admitted."""
            )
        }

        tserver.lsp_client.did_change(
           lsp.TextDocumentItem(
                uri=(project_root / filename).as_uri(),
                languageId=language_id,
                text=file_contents[filename],
                version=1,
           ),
           [lsp.TextDocumentContentChangeEvent.whole_document_change(file_contents[filename])]
        )
        # Diagnostics #####
        diagnostics = tserver.wait_for_message_of_type(lsp.PublishDiagnostics)
        assert diagnostics.uri == (project_root / filename).as_uri()
        diag_msgs = [diag.message for diag in diagnostics.diagnostics]

        if langserver_name == "coq-lsp":
            print(diag_msgs)
        else:
            raise ValueError(langserver_name)



def get_coq_output(coq_lsp_prog, coq_prog_args, contents, timeout_val, cwd=None, verbose_base=1, retry_with_debug_when=(lambda output: 'is not a compiled interface for this version of OCaml' in output), **kwargs):
    if timeout_val is not None and timeout_val < 0 and get_timeout(coq_lsp_prog) is not None:
        return get_coq_output(coq_lsp_prog, coq_prog_args, contents, get_timeout(coq_lsp_prog), cwd=cwd, verbose_base=verbose_base, retry_with_debug_when=retry_with_debug_when, **kwargs)



    key, file_name, cmds, input_val, cleaner = prepare_cmds_for_coq_output(coqc_prog, coqc_prog_args, contents, cwd=cwd, timeout_val=timeout_val, is_coqtop=is_coqtop, pass_on_stdin=pass_on_stdin, verbose_base=verbose_base, **kwargs)

    if key in COQ_OUTPUT.keys():
        cleaner()
        return COQ_OUTPUT[key][1]

    start = time.time()
    ((stdout, stderr), returncode) = memory_robust_timeout_Popen_communicate(kwargs['log'], cmds, stderr=subprocess.STDOUT, stdout=subprocess.PIPE, stdin=subprocess.PIPE, timeout=(timeout_val if timeout_val is not None and timeout_val > 0 else None), input=input_val, cwd=cwd)
    finish = time.time()
    runtime = finish - start
    kwargs['log']('\nretcode: %d\nstdout:\n%s\n\nstderr:\n%s\nruntime:\n%f\n\n' % (returncode, util.s(stdout), util.s(stderr), runtime),
                  level=verbose_base + 1)
    if get_timeout(coqc_prog) is None and timeout_val is not None:
        set_timeout(coqc_prog, 3 * max((1, int(math.ceil(finish - start)))), **kwargs)
    cleaner()
    COQ_OUTPUT[key] = (file_name, (clean_output(util.s(stdout)), tuple(cmds), returncode, runtime))
    kwargs['log']('Storing result: COQ_OUTPUT[%s]:\n%s' % (repr(key), repr(COQ_OUTPUT[key])),
                  level=verbose_base + 2)
    if retry_with_debug_when(COQ_OUTPUT[key][1][0]):
        debug_args = get_coq_debug_native_compiler_args(coqc_prog)
        kwargs['log']('Retrying with %s...' % ' '.join(debug_args),
                      level=verbose_base - 1)
        return get_coq_output(coqc_prog, list(debug_args) + list(coqc_prog_args), contents, timeout_val, cwd=cwd, is_coqtop=is_coqtop, pass_on_stdin=pass_on_stdin, verbose_base=verbose_base, retry_with_debug_when=(lambda output: False), **kwargs)
    return COQ_OUTPUT[key][1]
