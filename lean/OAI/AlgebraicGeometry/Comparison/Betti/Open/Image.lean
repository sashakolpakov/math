import OAI.AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback

/-! # Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.Image

noncomputable section

section

/-! For an actual open embedding, inverse image agrees with literal restriction to open images. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {M N : TopCat.{0}} (f : M ⟶ N) (hf : Topology.IsOpenEmbedding f)

def openRestriction : ConstantSheafSections.ComplexSheaves N ⥤ ConstantSheafSections.ComplexSheaves M := by
  have := hf.functor_isContinuous
  exact hf.functor.sheafPushforwardContinuous (ModuleCat.{0} ℂ)
    (Opens.grothendieckTopology M) (Opens.grothendieckTopology N)

instance openRestrictionAdditive : (openRestriction f hf).Additive where
  map_add := by intros; rfl

def openRestrictionAdjunction : openRestriction f hf ⊣ TopologicalSheafPullback.sheafDirectImage f := by
  have := hf.functor_isContinuous
  exact hf.isOpenMap.adjunction.sheafPushforwardContinuous
    (Opens.grothendieckTopology M) (Opens.grothendieckTopology N)

def openInverseImageIso : TopologicalSheafPullback.sheafInverseImage f ≅ openRestriction f hf :=
  (TopologicalSheafPullback.sheafImageAdjunction f).leftAdjointUniq (openRestrictionAdjunction f hf)

instance openRestrictionLimits : PreservesFiniteLimits (openRestriction f hf) :=
  preservesFiniteLimits_of_natIso (openInverseImageIso f hf)

instance openRestrictionColimits : PreservesFiniteColimits (openRestriction f hf) :=
  preservesFiniteColimits_of_natIso (openInverseImageIso f hf)

theorem openRestrictionAdjunction_unit (F : ConstantSheafSections.ComplexSheaves N) (U : Opens N) :
    ((openRestrictionAdjunction f hf).unit.app F).hom.app (op U) =
      F.obj.map (hf.isOpenMap.adjunction.counit.app U).op := rfl

theorem openInverseImageIso_unit (F : ConstantSheafSections.ComplexSheaves N) :
    (TopologicalSheafPullback.sheafImageAdjunction f).unit.app F ≫
        (TopologicalSheafPullback.sheafDirectImage f).map ((openInverseImageIso f hf).hom.app F) =
      (openRestrictionAdjunction f hf).unit.app F := by
  exact Adjunction.homEquiv_leftAdjointUniq_hom_app
    (TopologicalSheafPullback.sheafImageAdjunction f) (openRestrictionAdjunction f hf) F

end

section

/-! Sheafification commutes with literal restriction along actual open embeddings. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N : TopCat.{0}} (f : M ⟶ N) (hf : Topology.IsOpenEmbedding f)

def openPresheafRestriction : N.Presheaf (ModuleCat.{0} ℂ) ⥤ M.Presheaf (ModuleCat.{0} ℂ) :=
  (Functor.whiskeringLeft _ _ (ModuleCat.{0} ℂ)).obj hf.functor.op

def openPresheafDirectImage : M.Presheaf (ModuleCat.{0} ℂ) ⥤ N.Presheaf (ModuleCat.{0} ℂ) :=
  TopCat.Presheaf.pushforward (ModuleCat.{0} ℂ) f

instance openPresheafRestrictionAdditive : (openPresheafRestriction f hf).Additive where
  map_add := by intros; rfl

instance openPresheafDirectImageAdditive : (openPresheafDirectImage f).Additive where
  map_add := by intros; rfl

def openPresheafAdjunction : openPresheafRestriction f hf ⊣ openPresheafDirectImage f :=
  hf.isOpenMap.adjunction.op.whiskerLeft (ModuleCat.{0} ℂ)

def sheafificationOpenRestrictionIso :
    presheafToSheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ) ⋙ openRestriction f hf ≅
      openPresheafRestriction f hf ⋙ presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).comp
      (openRestrictionAdjunction f hf)).leftAdjointUniq
    ((openPresheafAdjunction f hf).comp
      (sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)))

end

/-! The literal presheaf restriction counit is invertible for an open embedding. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N : TopCat.{0}} (f : M ⟶ N) (hf : Topology.IsOpenEmbedding f)

theorem openPresheafCounit_isIso (P : M.Presheaf (ModuleCat.{0} ℂ)) :
    IsIso ((openPresheafAdjunction f hf).counit.app P) := by
  have : Mono f := (TopCat.mono_iff_injective f).mpr hf.injective
  have (U : Opens M) : IsIso (hf.isOpenMap.adjunction.unit.app U) := by infer_instance
  have (U : (Opens M)ᵒᵖ) : IsIso (((openPresheafAdjunction f hf).counit.app P).app U) := by
    change IsIso (P.map (hf.isOpenMap.adjunction.unit.app U.unop).op)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

theorem openPresheafComplexCounit_isIso (K : CochainComplex (M.Presheaf (ModuleCat.{0} ℂ)) ℤ) :
    IsIso ((Complex.Adjunction.onComplexes (openPresheafAdjunction f hf) (ComplexShape.up ℤ)).counit.app K) := by
  have (n : ℤ) : IsIso
      (((Complex.Adjunction.onComplexes (openPresheafAdjunction f hf) (ComplexShape.up ℤ)).counit.app K).f n) :=
    openPresheafCounit_isIso f hf (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.Image
