import OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheaf

/-! # Coefficient Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheafNaturality.CrystallineCoefficientSheafNaturality

noncomputable section

/-! # Naturality of the canonical coefficient-sheaf section isomorphism -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  (P Q : (Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} (WittVector p k))
  (hP : Presheaf.IsSheaf (Site.topology p k X) P)
  (hQ : Presheaf.IsSheaf (Site.topology p k X) Q) (f : P ⟶ Q)

local notation "Topology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheaf.CrystallineCoefficientSheaf.Modules p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k

theorem naturality :
    (CoefficientSheaf.CrystallineCoefficientSheaf.presheafIso p k X P hP).hom ≫ Functor.whiskerRight f E =
      ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).map f).hom ≫
        (CoefficientSheaf.CrystallineCoefficientSheaf.presheafIso p k X Q hQ).hom := by
  let g : CoefficientSheaf.CrystallineCoefficientSheaf.liftedSheaf p k X P hP ⟶
      CoefficientSheaf.CrystallineCoefficientSheaf.liftedSheaf p k X Q hQ := ⟨Functor.whiskerRight f E⟩
  have h := (sheafificationNatIso (J := Topology) (D := V)).symm.hom.naturality g
  exact congrArg
    (fun t : (presheafToSheaf Topology V).obj (P ⋙ E) ⟶
      CoefficientSheaf.CrystallineCoefficientSheaf.liftedSheaf p k X Q hQ => t.hom) h.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheafNaturality.CrystallineCoefficientSheafNaturality
