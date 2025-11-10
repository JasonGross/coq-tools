import os
import subprocess
import logging
from typing import Optional, Union

logger = logging.getLogger(__name__)

# Mimic the subprocess module's internal platform check
_IS_POSIX = os.name == "posix"


class Popen(subprocess.Popen):
    """
    A POSIX-only subclass of subprocess.Popen that captures resource usage
    information using os.wait4().

    This class provides two new methods and one new property:
      - wait4(timeout=None):
        Returns a tuple of (returncode, rusage).
      - communicate4(input=None, timeout=None):
        Returns a tuple of (stdout, stderr, rusage).
      - rusage (property):
        The resource usage object after the process has terminated.

    This class will raise NotImplementedError if instantiated on a non-POSIX
    system or one that lacks os.wait4().
    """

    def __init__(self, *args, allow_non_posix=False, **kwargs):
        """
        Initializes the Popen object and verifies system compatibility.
        """
        if not _IS_POSIX or not hasattr(os, "wait4"):
            if allow_non_posix:
                logger.warning(
                    "Popen with rusage is not supported on this system. Continuing anyway."
                )
            else:
                raise NotImplementedError(
                    "Popen with rusage is only supported on POSIX systems "
                    "with os.wait4() available. "
                    "Set allow_non_posix=True to continue anyway."
                )

        # This will be populated when the child process is reaped.
        self._rusage = None

        # Call the parent constructor.
        super().__init__(*args, **kwargs)

    @property
    def rusage(self):
        """The os.rusage object captured when the process terminated."""
        return self._rusage

    def _try_wait(self, wait_flags):
        """
        An override of the internal _try_wait method to use os.wait4()
        instead of os.waitpid(). This is the core of the modification.

        os.wait4() returns a 3-tuple: (pid, status, rusage) when a child
        terminates, or (0, 0) if WNOHANG is used and the child is still running.
        This method captures the rusage object and returns the expected
        (pid, status) tuple to the parent class's waiting logic.
        """
        if not hasattr(os, "wait4"):
            return super()._try_wait(wait_flags)
        try:
            # Call os.wait4() to get resource usage info.
            pid, sts, rusage = os.wait4(self.pid, wait_flags)
        except ChildProcessError:
            # This can happen if the process has already been reaped.
            # We mimic the behavior of the parent class in this case.
            return (self.pid, 0)

        # If the PID matches our child, it means the process has been
        # successfully waited on, so we store its resource usage.
        if pid == self.pid:
            self._rusage = rusage

        return (pid, sts)

    def wait4(self, timeout: Union[float, None] = None):
        """
        Waits for the child process to terminate.

        Args:
            timeout (float, optional): The time to wait in seconds. If None,
                                       waits indefinitely.

        Returns:
            tuple: A tuple containing (returncode, rusage_object).
        """
        # The parent's wait() method internally calls our overridden _try_wait(),
        # which populates self._rusage. We simply return the result along
        # with the captured rusage data.
        returncode = self.wait(timeout=timeout)
        return (returncode, self._rusage)

    def communicate4(
        self,
        input: Optional[Union[bytes, str]] = None,
        timeout: Union[float, None] = None,
    ):
        """
        Interacts with the process: sends data to stdin, reads from stdout/stderr,
        and waits for termination.

        Args:
            input (bytes or str, optional): Data to be sent to stdin.
            timeout (float, optional): The timeout in seconds for the entire
                                       communication.

        Returns:
            tuple: A tuple containing (stdout_data, stderr_data, rusage_object).
        """
        # The parent's communicate() method also calls wait() internally,
        # which triggers our _try_wait() override.
        stdout, stderr = self.communicate(input=input, timeout=timeout)
        return (stdout, stderr, self._rusage)
