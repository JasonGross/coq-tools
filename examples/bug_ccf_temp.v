
 
Definition LocallySmallSpecializedCategory (obj : Type)   := SpecializedCategory obj.
  Definition OppositeComputationalCategory `(C : @ComputationalCategory objC) : ComputationalCategory objC :=
    @Build_ComputationalCategory objC
                                 (fun s d => Morphism C d s)
                                 (Identity (C := C))
                                 (fun _ _ _ m1 m2 => Compose m2 m1).

  Definition OppositeCategory `(C : @SpecializedCategory objC) : @SpecializedCategory objC :=
    @Build_SpecializedCategory' objC
                                (OppositeComputationalCategory (UnderlyingCCategory C))
                                _.
  Definition SwapFunctor `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD)
  : SpecializedFunctor (C * D) (D * C)
    := Build_SpecializedFunctor (C * D) (D * C)
                                (fun cd => (snd cd, fst cd))
                                (fun _ _ m => (snd m, fst m))
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
  Definition ProductLaw1Functor : SpecializedFunctor (C * 1) C
    := Eval hnf in ProductLaw1Functor'.
  Definition LocallySmallCat := ComputableCategory _ LSUnderlyingCategory.

  Definition CommaSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_CommaSpecializedCategory_Object.

  Definition CommaCategoryInducedFunctor s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
    := Eval cbv beta iota zeta delta [CommaCategoryInducedFunctor''] in @CommaCategoryInducedFunctor'' s d m.

  Definition LocallySmallCatOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval cbv beta iota zeta delta [LocallySmallCatOverInducedFunctor'''] in @LocallySmallCatOverInducedFunctor''' _ _ m.
  Local Transparent LocallySmallCat.
End LocallySmallCatOverInducedFunctor.


Section CommaCategoryProjectionFunctor.
  Context `(A : LocallySmallSpecializedCategory objA).
  Context `(B : LocallySmallSpecializedCategory objB).
  Context `(C : SpecializedCategory objC).

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

  Definition CommaCategoryProjectionFunctor_ObjectOf (ST : (OppositeCategory (C ^ A)) * (C ^ B)) :
    LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)
    := let S := (fst ST) in
       let T := (snd ST) in
       existT _
              ((S ↓ T : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt)
              (CommaCategoryProjection S T) :
         CommaSpecializedCategory_ObjectT (IdentityFunctor _)
                                          (SliceSpecializedCategory_Functor LocallySmallCat
                                                                            (A * B : LocallySmallSpecializedCategory _)).

  Definition CommaCategoryProjectionFunctor_MorphismOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    Morphism (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
             (CommaCategoryProjectionFunctor_ObjectOf s)
             (CommaCategoryProjectionFunctor_ObjectOf d).
    hnf in *; constructor; simpl in *.
    exists (CommaCategoryInducedFunctor m, @unit_eq _ _).
    abstract (
        simpl;
        functor_eq;
        destruct_head_hnf @CommaSpecializedCategory_Morphism;
        destruct_sig;
        reflexivity
      ).
  Defined.

  Lemma CommaCategoryProjectionFunctor_FIdentityOf x :
    CommaCategoryProjectionFunctor_MorphismOf (Identity x) = Identity _.
      Time (expand; anihilate).
 
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m' :
    CommaCategoryProjectionFunctor_MorphismOf (@Compose _ _ s d d' m m')
    = Compose (CommaCategoryProjectionFunctor_MorphismOf m)
              (CommaCategoryProjectionFunctor_MorphismOf m').
      Time (expand; anihilate).
 
  Qed.

  Definition CommaCategoryProjectionFunctor :
    SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                       (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)).
    refine (Build_SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                                     (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
                                     CommaCategoryProjectionFunctor_ObjectOf
                                     CommaCategoryProjectionFunctor_MorphismOf
                                     _
                                     _);
    intros;
    [ apply CommaCategoryProjectionFunctor_FCompositionOf
    | apply CommaCategoryProjectionFunctor_FIdentityOf ].
  Defined.
End CommaCategoryProjectionFunctor.

Section SliceCategoryProjectionFunctor.
  Context `(C : LocallySmallSpecializedCategory objC).
  Context `(D : SpecializedCategory objD).

  Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf / .
  Local Arguments ComposeFunctors / .
  Local Arguments LocallySmallCatOverInducedFunctor / .
   
  Local Arguments CommaCategoryProjectionFunctor / .
  Local Arguments SwapFunctor / .
  Local Arguments ExponentialLaw1Functor_Inverse / .
  Local Arguments IdentityFunctor / .
 

  Definition SliceCategoryProjectionFunctor_pre_pre'
    := Eval hnf in (LocallySmallCatOverInducedFunctor (ProductLaw1Functor C : Morphism LocallySmallCat (C * 1 : LocallySmallSpecializedCategory _) C)).

  Definition SliceCategoryProjectionFunctor_pre_pre : SpecializedFunctor (LocallySmallCat / (C * 1 : LocallySmallSpecializedCategory _)) (LocallySmallCat / C).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre_pre'.
  Defined.

  Arguments SliceCategoryProjectionFunctor_pre_pre / .

 
   

  Definition SliceCategoryProjectionFunctor_pre' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D)).
     
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre_pre) in
    exact F.
 
  Defined.

  Definition SliceCategoryProjectionFunctor_pre'' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre'.
  Defined.

  Definition SliceCategoryProjectionFunctor_pre := Eval hnf in SliceCategoryProjectionFunctor_pre''.

  Definition SliceCategoryProjectionFunctor' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre) in
    exact F.
  Defined.

  Definition SliceCategoryProjectionFunctor'' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor'.
  Defined.

  Definition SliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))
    := Eval cbv beta iota zeta delta [SliceCategoryProjectionFunctor''] in SliceCategoryProjectionFunctor''.
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _) D)).
    refine (LocallySmallCatOverInducedFunctor _).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.


