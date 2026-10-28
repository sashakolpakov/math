import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeCoefficientUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows

/-! # Supported Open Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenScalar

noncomputable section

/-! Functions on the affine source open act on the genuine original
supported cohomology. The selected-support candidate preserves this
action by naturality through the actual restriction unit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mapped_single_isIso {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] (F : A ⥤ B) [F.Additive]
    {M N : A} (f : M ⟶ N) [IsIso (F.map f)] (c : ℕ) :
    IsIso ((F.mapHomologicalComplex (.up ℕ)).map ((single A (.up ℕ) c).map f)) := by
  have : IsIso ((F ⋙ single B (.up ℕ) c).map f) := by
    change IsIso ((single B (.up ℕ) c).map (F.map f))
    infer_instance
  exact IsIso.of_isIso_fac_right ((singleMapHomologicalComplex F (.up ℕ) c).hom.naturality f)

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeCoefficientUnit
variable {Y : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Y.Opens) (V : Y.Opens) (hF : ∀ r, F.obj r ≤ V)
  {ι : Type} [LinearOrder ι] (W : ι → C) (N : Y.Modules) (c : ℕ)

include hF in
theorem sourceMap_isIso : IsIso (AffinePrincipal.Injective.Comparison.sourceMap F W N c (Open.SubschemeCoefficientUnit.unit V N)) := by
  let S := AffinePrincipal.Injective.Comparison.coefficients F
  let a := (SheafOfModules.toSheaf Y.ringCatSheaf).map (Open.SubschemeCoefficientUnit.unit V N)
  have : IsIso (S.map a) := Open.SubschemeCoefficientUnit.diagramMap_isIso V N F hF
  have : IsIso ((S.mapHomologicalComplex (.up ℕ)).map ((single _ (.up ℕ) c).map a)) :=
    mapped_single_isIso S a c
  let T := (AugmentedOrdered.CechFunctor.functor W (D := AddCommGrpCat)).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat (.up ℕ) (.up ℕ) (.up ℕ)
  change IsIso (T.map ((S.mapHomologicalComplex (.up ℕ)).map ((single _ (.up ℕ) c).map a)))
  infer_instance

def unitIso (q : ℕ) : (AffinePrincipal.Injective.Comparison.source F W N c).homology q ≅
    (AffinePrincipal.Injective.Comparison.source F W (Open.SubschemeCoefficientUnit.extension V N) c).homology q :=
  letI := sourceMap_isIso F V hF W N c
  homologyMapIso (asIso (AffinePrincipal.Injective.Comparison.sourceMap F W N c (Open.SubschemeCoefficientUnit.unit V N))) q

def action (z : Γ(Y,V)) (q : ℕ) : (AffinePrincipal.Injective.Comparison.source F W N c).homology q ⟶ (AffinePrincipal.Injective.Comparison.source F W N c).homology q :=
  (unitIso F V hF W N c q).hom ≫
    homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W (Open.SubschemeCoefficientUnit.extension V N) c (Open.SubschemeCoefficientUnit.scalar V N z)) q ≫
      (unitIso F V hF W N c q).inv

variable (G : C ⥤ Y.Opens) (hG : ∀ r, G.obj r ≤ V) (O₁ O₂ : Y.Opens)
  (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions F G W O₁ O₂)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G]
  [N.IsQuasicoherent] [(Open.SubschemeCoefficientUnit.extension V N).IsQuasicoherent]

theorem candidate_unit (q : ℕ) :
    H.candidate N c q ≫ (unitIso F V hF W N c q).hom =
      (unitIso G V hG W N c q).hom ≫ H.candidate (Open.SubschemeCoefficientUnit.extension V N) c q :=
  (H.candidate_natural N c (Open.SubschemeCoefficientUnit.unit V N) q).symm

theorem candidate_fixed (z : Γ(Y,V)) (q : ℕ) (x : (AffinePrincipal.Injective.Comparison.source G W N c).homology q)
    (hx : action G V hG W N c z q x = x) :
    action F V hF W N c z q (H.candidate N c q x) = H.candidate N c q x := by
  let eF := unitIso F V hF W N c q
  let eG := unitIso G V hG W N c q
  have hx' := congrArg eG.hom hx
  change eG.hom (eG.inv (homologyMap
    (AffinePrincipal.Injective.Comparison.sourceMap G W (Open.SubschemeCoefficientUnit.extension V N) c (Open.SubschemeCoefficientUnit.scalar V N z)) q (eG.hom x))) = eG.hom x at hx'
  rw [Iso.inv_hom_id_apply] at hx'
  have hn := ConcreteCategory.congr_hom
    (H.candidate_natural N c (Open.SubschemeCoefficientUnit.unit V N) q) x
  change H.candidate (Open.SubschemeCoefficientUnit.extension V N) c q (eG.hom x) = eF.hom (H.candidate N c q x) at hn
  have hf := H.candidate_fixed (Open.SubschemeCoefficientUnit.extension V N) c (Open.SubschemeCoefficientUnit.scalar V N z) q (eG.hom x) hx'
  change eF.inv (homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W (Open.SubschemeCoefficientUnit.extension V N) c (Open.SubschemeCoefficientUnit.scalar V N z)) q
    (eF.hom (H.candidate N c q x))) = H.candidate N c q x
  rw [← hn, hf, hn, Iso.hom_inv_id_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenScalar
