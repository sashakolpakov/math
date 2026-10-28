import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HyperplanePowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Intrinsic Projective Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicProjectivePowers

noncomputable section

/-! Compare ProjectiveCohomology's concrete projective twists with the multilinear tensor
powers used for the polarization, by their actual universal properties. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

universe u
variable (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1))
attribute [local instance] MvPolynomial.gradedAlgebra
local instance c44NativeProjectivePowersMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def hyperplanePowerMultilinearIso : ∀ m : ℕ,
    SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m ≅
      Picard.Homomorphisms.TensorPowerSheaf.Construction.tensorPowerSheaf (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) m
  | 0 => SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _ ≪≫ Classical.choice
      ((Picard.Homomorphisms.TensorPowerGroup.Construction.unit_isTensorPower_zero _).unique (Picard.Homomorphisms.TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower _ 0))
  | m + 1 =>
      SheafCohomology.Projective.TensorSections.monoidalTensorObjIso _ _ ≪≫
        AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (hyperplanePowerMultilinearIso m) (Iso.refl _) ≪≫
          (Picard.Homomorphisms.TensorPowerGroup.Construction.tensorPowerSuccIso _ m).symm

def nativeHyperplanePowerIso (m : ℕ) :
    SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m ≅
      ((Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine R n j).tensorPower m).sheaf :=
  PolarizationEmbedding.hyperplanePowerMultilinearIso R n j m ≪≫ Classical.choice
    ((Picard.Homomorphisms.TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower _ m).unique
      ((Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine R n j).tensorPower_isTensorPower m))

variable {R n j}

theorem nativeHyperplane_section_pullback {X S : Scheme.{0}} (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (f : X ⟶ S)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) (j : Fin (n + 1)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(S, ⊤)) j m) ≅
        (P.tensorPower m).sheaf) := by
  obtain ⟨e⟩ := Projective.HyperplanePowers.PolarizationEmbedding.sectionHyperplane_power_iso P f s hs j m
  exact ⟨(Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).mapIso
    (nativeHyperplanePowerIso Γ(S, ⊤) n j m) ≪≫ e⟩

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicProjectivePowers
