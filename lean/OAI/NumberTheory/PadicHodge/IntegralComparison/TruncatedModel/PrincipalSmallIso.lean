import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.AmbientIsomorphism

/-! # Principal Small Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSmallIso

noncomputable section

/-! The actual principal affine chart is the original crystalline
localization, including its reduction and divided powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem localization_bijective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) [IsLocalization.Away r S]
    (f : Localization.Away r →+* S)
    (hf : ∀ x, f (algebraMap R (Localization.Away r) x) = algebraMap R S x) :
    Function.Bijective f := by
  let e := IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) S
  have he : f = e.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    exact (hf x).trans (e.commutes x).symm
  rw [he]
  exact e.bijective

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp
local notation "Q" => Functor.obj N U

theorem ambient_bijective (r : C) :
    Function.Bijective (PrincipalFrame.map p k n X Y f hp U r).ambientMap := by
  let : IsLocalization.Away r.val Γ(X.left, X.left.basicOpen r.val) :=
    U.property.isLocalization_basicOpen r.val
  apply localization_bijective (S := Γ(X.left, X.left.basicOpen r.val)) r.val
    (PrincipalFrame.map p k n X Y f hp U r).ambientMap.toRingHom
  intro x
  exact (RingHom.congr_fun (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.ambientLift_comp p k Y
    (PrincipalFrame.projection p k n X Y f hp U r) r.val
    (PrincipalFrame.coefficient_unit p k n X Y f hp U r)) x).trans
      (SmallFrame.map_ambient p k n X Y f hp
        (AffinePrincipal.Diagram.projection X.left U.val U.property r) x)

def iso (r : C) : (PrincipalFrame.frames p k n X Y f hp U).obj r ≅
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k Y Q r :=
  Crystalline.AmbientIsomorphism.iso p k Y
    (PrincipalFrame.map p k n X Y f hp U r)
    (ambient_bijective p k n X Y f hp U r)

instance map_isIso (r : C) : IsIso (PrincipalFrame.map p k n X Y f hp U r) :=
  inferInstanceAs (IsIso (iso p k n X Y f hp U r).hom)

instance transformation_isIso : IsIso (PrincipalFrame.transformation p k n X Y f hp U) := by
  let (r : C) : IsIso ((PrincipalFrame.transformation p k n X Y f hp U).app r) :=
    map_isIso p k n X Y f hp U r
  exact NatIso.isIso_of_isIso_app _

def diagramIso : PrincipalFrame.frames p k n X Y f hp U ≅
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k Y Q :=
  asIso (PrincipalFrame.transformation p k n X Y f hp U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSmallIso
