import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedCoefficientPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.SectionEvaluation

/-! # Coefficient Weight -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientWeight

noncomputable section

/-! The weight in the original finite projective point fraction is the
literal value of the coefficient at the source section, lifted by the
base algebra map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y) [IsClosedImmersion (s₀ ≫ f)]
  (hbase : (s₀ ≫ f) ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ ((s₀ ≫ f) ≫ i) ⁻¹ᵁ U)
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    ((s₀ ≫ f) ≫ i).ker.ideal ⟨U,hU⟩)
local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U
local instance coefficient_qc : (Cech.StructurePullbackUnit.coefficients f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i
local instance coefficient_finite : (Cech.StructurePullbackUnit.coefficients f i).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f i

omit [IsNoetherianRing R] [IsFinite f] in
theorem value (x : Finite.FlatCoefficientSections.coefficientRing f i U) :
    Projective.FixedCoefficientPointFraction.scalar i (s₀ ≫ f) hbase
      (Cech.StructurePullbackUnit.coefficients f i) (Cech.SectionCoefficientUnit.sheafMap s₀ f i)
      U hU hcontains s t hst (Finite.FlatCoefficientSections.coefficientRing f i U) (Finite.FlatCoefficientSections.chartIso f i U hU) x =
    algebraMap R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
        (s₀.appLE (f ⁻¹ᵁ (i ⁻¹ᵁ U)) ⊤ hcontains x)) := by
  have hz : ((s₀ ≫ f) ≫ i) ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = 𝟙 _ :=
    (Category.assoc _ _ _).trans hbase
  exact congrArg (algebraMap R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
    (FiniteCoefficient.SectionEvaluation.evaluation R
      (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) s₀ f i hz U hU hcontains s t hst x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientWeight
