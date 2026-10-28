import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.IntrinsicDualCoordinates

/-! # Coefficient Residue Dimension Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimensionData

noncomputable section

/-! The actual finite-coefficient residue and adjunction maps with an
arbitrary ambient projective dimension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g N : ℕ} (h : c+g=N)
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] ProjectiveCoefficient.HomLocal.scalar_terms
  ProjectiveCoefficient.HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (N+1)) (B : ℕ) (hB : N+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (k : Fin (N+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (List.ofFn s))
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U))
  (b : Basis (Fin N) Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)⁄R])

include h hB in
omit [Smooth X.hom] [IsProper X.hom] in
theorem exactAt (q : ℕ) (hq : q ≠ c) : (ProjectiveCoefficient.HomLocal.coefficientDual X f i j B).ExactAt q := by
  let : SmoothOfRelativeDimension g (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
    change SmoothOfRelativeDimension g (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R N).hom)
    rw [Over.w i]
    infer_instance
  apply CoefficientPurity.exactAt f i.left j B (N+1) hB g q
  simp only [Fintype.card_fin, Nat.add_sub_cancel_right]
  have hc : N-g=c := by omega
  simpa only [hc] using hq

abbrev sourceComplex :=
  ((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj
    (ProjectiveCoefficient.HomLocal.coefficientDual X f i j B)

abbrev structureSingle :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) (.up ℕ) c).obj
    (Principal.ClosedKoszulResidue.target i.left U hU)

abbrev formSingle :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) (.up ℕ) c).obj
    ((Principal.ModuleFunctor.functor U hU).obj (ProjectiveCoefficient.HomLocal.formSheaf X i g))

abbrev survivorSingle :=
  ((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj
    ((single (Projective.IntrinsicOverlap.Intrinsic.space R N).Modules (.up ℕ) c).obj ((ProjectiveCoefficient.HomLocal.coefficientDual X f i j B).homology c))

abbrev principalSurvivorSingle :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) (.up ℕ) c).obj
    ((Principal.ModuleFunctor.functor U hU).obj ((ProjectiveCoefficient.HomLocal.coefficientDual X f i j B).homology c))

abbrev homSingle :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) (.up ℕ) c).obj
    ((Principal.ModuleFunctor.functor U hU).obj (ProjectiveCoefficient.HomLocal.targetSheaf X f i g))

def residue (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    sourceComplex X f i j B U hU ⟶ structureSingle (c := c) X i U hU := by
  letI : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent f i.left
  letI : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType f i.left
  letI : (ProjectiveCoefficient.HomLocal.canonical (R := R) j).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (N+1))
  letI (r : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_term_projective X f i j B U hU k hUk r
  letI : Algebra
      (Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) s)
      (Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
    FiniteCoefficient.QuotientAction.algebra f i.left U hU s hs
  letI : IsScalarTower Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)
      (Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) s)
      (Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
    FiniteCoefficient.QuotientAction.tower f i.left U hU s hs
  let ε := Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.coefficient X f i) j B
  let P := Principal.Resolution.Comparison.resolution U hU (ProjectiveCoefficient.HomLocal.coefficient X f i)
    (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B) ε (ModuleCat.of Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (Finite.FlatCoefficientSections.coefficientRing f i.left U))
    (Finite.FlatCoefficientSections.chartIso f i.left U hU)
  exact Principal.IntrinsicDualCoordinates.Intrinsic.map U hU (ProjectiveCoefficient.HomLocal.canonical j) (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B)
    (Principal.CoefficientResidueData.map U hU (ProjectiveCoefficient.HomLocal.canonical j)
    (Projective.PrincipalResidueCoordinates.scalarFrame (c := N) (g := 0) j U hU k hUk b)
    (ProjectiveCoefficient.HomLocal.coefficient X f i) (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B) ε
    (ModuleCat.of Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (Finite.FlatCoefficientSections.coefficientRing f i.left U))
    (Finite.FlatCoefficientSections.chartIso f i.left U hU) P i.left s hs hreg
    (Koszul.CoefficientPointFraction.vector Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) s (Finite.FlatCoefficientSections.coefficientRing f i.left U) x))

def symbol : structureSingle (c := c) X i U hU ⟶ formSingle (c := c) (g := g) X i U hU :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)) (.up ℕ) c).map
    (Principal.DifferentialSymbol.map R X (Projective.IntrinsicOverlap.Intrinsic.model R N) i U hU g (fun a => i.left.app U (t a)))

variable {ι : Type u} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)

def concentration :
    (Supported.CechHomotopyEquivalence.functor W q).obj (sourceComplex X f i j B U hU) ≅
      (Supported.CechHomotopyEquivalence.functor W q).obj
        (survivorSingle (c := c) X f i j B U hU) := by
  letI (r : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB r
  exact PrincipalReference.Concentration.Reference.iso U hU W (ProjectiveCoefficient.HomLocal.coefficientDual X f i j B)
    c (exactAt h X f i j B hB) q

def homologyToPrincipal :
    survivorSingle (c := c) X f i j B U hU ⟶ principalSurvivorSingle (c := c) X f i j B U hU :=
  (singleMapHomologicalComplex (Principal.ModuleFunctor.functor U hU) (.up ℕ) c).hom.app
    ((ProjectiveCoefficient.HomLocal.coefficientDual X f i j B).homology c)

def homMap :
    principalSurvivorSingle (c := c) X f i j B U hU ⟶ homSingle (c := c) (g := g) X f i U hU :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)) (.up ℕ) c).map
    ((Principal.ModuleFunctor.functor U hU).map
      (ProjectiveCoefficient.HomDegreeCoordinates.iso X f i g c (by omega) j B hB (by omega)).hom)

def evaluation (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    homSingle (c := c) (g := g) X f i U hU ⟶ formSingle (c := c) (g := g) X i U hU :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)) (.up ℕ) c).map
    (Principal.HomEvaluation.map U hU (ProjectiveCoefficient.HomLocal.coefficient X f i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) x)

def leftMap (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    (Supported.CechHomotopyEquivalence.functor W q).obj (sourceComplex X f i j B U hU) ⟶
      (Supported.CechHomotopyEquivalence.functor W q).obj
        (formSingle (c := c) (g := g) X i U hU) :=
  (Supported.CechHomotopyEquivalence.functor W q).map
      (residue X f i j B U hU k hUk s hs hreg b x) ≫
    (Supported.CechHomotopyEquivalence.functor W q).map (symbol (c := c) X i U hU t)

def rightMap (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    (Supported.CechHomotopyEquivalence.functor W q).obj (sourceComplex X f i j B U hU) ⟶
      (Supported.CechHomotopyEquivalence.functor W q).obj
        (formSingle (c := c) (g := g) X i U hU) :=
  (concentration h X f i j B hB U hU W q).hom ≫
    (Supported.CechHomotopyEquivalence.functor W q).map
      (homologyToPrincipal (c := c) X f i j B U hU) ≫
    (Supported.CechHomotopyEquivalence.functor W q).map (homMap h X f i j B hB U hU) ≫
    (Supported.CechHomotopyEquivalence.functor W q).map (evaluation (c := c) (g := g) X f i U hU x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimensionData
