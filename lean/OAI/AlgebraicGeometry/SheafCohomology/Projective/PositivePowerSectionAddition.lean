import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence

/-! # Positive Power Section Addition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerSectionAddition.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Addition of twist degrees preserves the canonical tensor-power sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
open OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance positiveSectionAdditionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateHyperplanePoleSheafPower_addIso_section (j : σ) (m n : ℕ) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n).hom.val.app (op ⊤)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (m + n)) =
      TensorSections.tensorSection (X := Proj (homogeneousSubmodule σ R))
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) ⊤
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n) := by
  induction n with
  | zero =>
      change (ρ_ (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)).inv.val.app (op ⊤)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m) = _
      have h := GlobalTensorSectionCoherence.rightUnitor_tensorSection_top (X := Proj (homogeneousSubmodule σ R))
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m)
      have hh := congrArg
        (fun x => (ρ_ (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)).inv.val.app (op ⊤) x) h
      have hc := SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT
        (ρ_ (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)).symm (op ⊤)
        (TensorSections.tensorSection (X := Proj (homogeneousSubmodule σ R))
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
          (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules) ⊤
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m)
          (TensorSections.monoidalUnitSection _))
      exact hh.symm.trans hc
  | succ n ih =>
      let S := Proj (homogeneousSubmodule σ R)
      let M : S.Modules := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m
      let N : S.Modules := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
      let P : S.Modules := HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j
      let Q : S.Modules := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n)
      let g : Q ⟶ M ⊗ N := (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n).hom
      let x : Γ(M, ⊤) := TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m
      let y : Γ(N, ⊤) := TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n
      let z : Γ(P, ⊤) := HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j
      let t : Γ(Q, ⊤) := TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (m + n)
      let a : Γ((M ⊗ N) ⊗ P, ⊤) → Γ(M ⊗ (N ⊗ P), ⊤) :=
        (α_ M N P).hom.val.app (op ⊤)
      have hI : g.val.app (op ⊤) t = TensorSections.tensorSection (X := S) M N ⊤ x y := ih
      have hm : (g ⊗ₘ 𝟙 P).val.app (op ⊤) (TensorSections.tensorSection (X := S) Q P ⊤ t z) =
          TensorSections.tensorSection (X := S) (M ⊗ N) P ⊤ (g.val.app (op ⊤) t) z :=
        TensorFrameSections.tensorSection_map (X := S) g (𝟙 P) ⊤ t z
      exact (congrArg a hm).trans
        ((congrArg (fun s => a (TensorSections.tensorSection (X := S) (M ⊗ N) P ⊤ s z)) hI).trans
          (GlobalTensorSectionCoherence.associator_tensorSection_top (X := S) M N P x y z))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerSectionAddition.MvPolynomial
