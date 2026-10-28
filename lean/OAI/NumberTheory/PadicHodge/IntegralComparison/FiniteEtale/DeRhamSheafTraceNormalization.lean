import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTrace

/-! # De Rham Sheaf Trace Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTraceNormalization

noncomputable section

/-! The global trace agrees with the native local chain trace in every
affine étale chart with a free coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis

universe u v

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  (U : Y.left.Opens) [Fact (IsAffineOpen U)]
  (σ : Type u) [Fintype σ] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]

local instance : Algebra (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R X Y f U

variable {ι : Type v} [Fintype ι] (b : Module.Basis ι (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U))

theorem trace_app_of_chart (n : ℕ) :
    ((DeRhamSheafTrace.trace R X Y f).f n).hom.app (op U) = (AffineOpen.DeRhamTrace.map R X Y f U σ b).f n := by
  let i : TraceBasis.Index R X Y f := ⟨U, Fact.out,
    ⟨σ, inferInstance, inferInstance, inferInstance, inferInstance⟩,
    Module.Free.of_basis b⟩
  let : LinearOrder (TraceBasis.coordinateIndex R X Y f i) := TraceBasis.coordinateOrder R X Y f i
  let : Module.Free (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) := TraceBasis.sourceFree R X Y f i
  let : Module.Finite (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) := TraceBasis.sourceFinite R X Y f i
  let : Algebra (MvPolynomial (TraceBasis.coordinateIndex R X Y f i) R) (AffineOpen.DeRhamTrace.targetRing R Y U) :=
    TraceBasis.polynomialAlgebra R X Y f i
  let : IsScalarTower R (MvPolynomial (TraceBasis.coordinateIndex R X Y f i) R) (AffineOpen.DeRhamTrace.targetRing R Y U) :=
    TraceBasis.coordinateTower R X Y f i
  let : Algebra.Etale (MvPolynomial (TraceBasis.coordinateIndex R X Y f i) R) (AffineOpen.DeRhamTrace.targetRing R Y U) :=
    TraceBasis.coordinateEtale R X Y f i
  have h := DeRhamSheafTrace.trace_app R X Y f i n
  have hc := AffineOpen.DeRhamTrace.map_coordinate_independent R X Y f U (TraceBasis.coordinateIndex R X Y f i)
    (Module.Free.chooseBasis (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)) σ b
  exact h.trans (congrArg (fun t => t.f n) hc)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTraceNormalization
