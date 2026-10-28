import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelLieRank
import OAI.RepresentationTheory.Theta.Geometric.TangentAddition
import OAI.RepresentationTheory.Theta.Geometric.DiagonalExtension

/-! # Geometric Lie Rank -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GeometricLieRank

/-! Extend the reference fiber's actual native tangent comparison to
every complex residue-field extension, retaining the diagonal CM action. -/

open scoped TensorProduct _root_.CategoryTheory.MonObj _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.integralCharacters (P : Datum.RankThreePELDatum E s) (p : Fin s × Fin 3) :
    NumberField.RingOfIntegers E →+* ℂ :=
  (P.quotientCharacter p.1 p.2).comp (algebraMap (NumberField.RingOfIntegers E) E)

namespace ReferenceAlgebraicModel

variable (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeLieChart : RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart M.abelian.toOver 1 := RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.nativeTangentChart M.abelian.toOver 1

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.flatPeriodCoordinates : ((Fin s × Fin 3) → ℂ) ≃ₗ[ℂ]
    Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s) where
  toFun v i j := v (i, j)
  invFun v p := v p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.flatPeriodDifferential : ((Fin s × Fin 3) → ℂ) ≃ₗ[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
  (AlgebraicModel.ReferenceAlgebraicModel.flatPeriodCoordinates (s := s)).trans
    ((F.quotientCoordinatesEquiv hP).symm.trans M.periodDifferential.toLinearEquiv)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.flatPeriodDifferential_action (a : NumberField.RingOfIntegers E)
    (v : (Fin s × Fin 3) → ℂ) :
    M.actionDifferential a (M.flatPeriodDifferential v) =
      M.flatPeriodDifferential (RepresentationTheory.Theta.Geometric.DiagonalExtension.diagonalOperator P.integralCharacters a v) := by
  have he : F.action a ((F.quotientCoordinatesEquiv hP).symm (AlgebraicModel.ReferenceAlgebraicModel.flatPeriodCoordinates v)) =
      (F.quotientCoordinatesEquiv hP).symm
        (AlgebraicModel.ReferenceAlgebraicModel.flatPeriodCoordinates (RepresentationTheory.Theta.Geometric.DiagonalExtension.diagonalOperator P.integralCharacters a v)) := by
    apply (F.quotientCoordinatesEquiv hP).injective
    rw [F.quotientCoordinatesEquiv_action hP, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  exact (M.periodDifferential_action a _).trans (congrArg M.periodDifferential he)

variable (k : Type) [Field k] [Algebra ℂ k]

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricPeriodDifferential : ((Fin s × Fin 3) → k) ≃ₗ[k] k ⊗[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
  RepresentationTheory.Theta.Geometric.DiagonalExtension.extendedDiagonalEquiv k M.flatPeriodDifferential

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricPeriodTangentEquiv : ((Fin s × Fin 3) → k) ≃
    RepresentationTheory.Theta.Geometric.TangentSources.extendedSchemeTangentPoints ℂ k M.abelian.toOver (RepresentationTheory.Theta.Geometric.ExtendedComplexPoints.extendedComplexPoint k 1) :=
  (M.geometricPeriodDifferential k).toEquiv.trans (M.nativeLieChart.geometricTangentEquiv k)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricPeriodDifferential_action (a : NumberField.RingOfIntegers E)
    (v : (Fin s × Fin 3) → k) :
    (M.actionDifferential a).toLinearMap.baseChange k (M.geometricPeriodDifferential k v) =
      M.geometricPeriodDifferential k
        (RepresentationTheory.Theta.Geometric.DiagonalExtension.diagonalOperator (fun p => (algebraMap ℂ k).comp (P.integralCharacters p)) a v) :=
  RepresentationTheory.Theta.Geometric.DiagonalExtension.extendedDiagonal_intertwining P.integralCharacters k M.flatPeriodDifferential
    (fun a => (M.actionDifferential a).toLinearMap) M.flatPeriodDifferential_action a v

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricPeriodTangent_action (a : NumberField.RingOfIntegers E)
    (v : (Fin s × Fin 3) → k) :
    (M.geometricPeriodTangentEquiv k
      (RepresentationTheory.Theta.Geometric.DiagonalExtension.diagonalOperator (fun p => (algebraMap ℂ k).comp (P.integralCharacters p)) a v)).val =
        (M.geometricPeriodTangentEquiv k v).val ≫ M.integralAction.map a := by
  exact (congrArg (fun w : k ⊗[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian =>
      (M.nativeLieChart.geometricTangentEquiv k w).val)
      (M.geometricPeriodDifferential_action k a v)).symm.trans
    (M.nativeLieChart.geometricGroup_naturality k M.nativeLieChart
      (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.geometricPeriodDifferential k v))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricPeriodTangent_add (v w : (Fin s × Fin 3) → k) :
    (M.geometricPeriodTangentEquiv k (v + w)).val =
      (M.geometricPeriodTangentEquiv k v).val * (M.geometricPeriodTangentEquiv k w).val :=
  (congrArg (fun u : k ⊗[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian =>
    (M.nativeLieChart.geometricTangentEquiv k u).val)
    ((M.geometricPeriodDifferential k).map_add v w)).trans
      (M.nativeLieChart.geometricTangentEquiv_add k _ _)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricPeriodTangent_smul (c : k) (v : (Fin s × Fin 3) → k) :
    (M.geometricPeriodTangentEquiv k (c • v)).val =
      RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ k c ≫ (M.geometricPeriodTangentEquiv k v).val :=
  (congrArg (fun u : k ⊗[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian =>
    (M.nativeLieChart.geometricTangentEquiv k u).val)
    ((M.geometricPeriodDifferential k).map_smul c v)).trans
      (M.nativeLieChart.geometricTangentEquiv_smul k c _)

end ReferenceAlgebraicModel

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GeometricLieRank

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GeometricLieRank.ReferenceAlgebraicModel

/-! Geometric Lie eigenpoints of the constructed models have the exact
prescribed signature over every extended complex residue field. -/

open scoped TensorProduct _root_.CategoryTheory.MonObj Classical
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

variable (k : Type) [Field k] [Algebra ℂ k] (τ : E →+* ℂ)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter : NumberField.RingOfIntegers E →+* k :=
  (algebraMap ℂ k).comp (τ.comp (algebraMap (NumberField.RingOfIntegers E) E))

abbrev _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal := RepresentationTheory.Theta.Geometric.DiagonalEigen.diagonalEigenSpace
  (fun p : Fin s × Fin 3 => (algebraMap ℂ k).comp (P.integralCharacters p))
  (AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k τ)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricLieEquiv : AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal (P := P) k τ ≃
    RepresentationTheory.Theta.Geometric.LieFieldTests.extendedLieEigenpoints ℂ k M.abelianScheme M.integralAction (AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k τ) where
  toFun v := ⟨(M.geometricPeriodTangentEquiv k v.val).val, by
    constructor
    · exact (M.geometricPeriodTangentEquiv k v.val).property.trans (MonObj.comp_one _)
    · intro a
      exact (M.geometricPeriodTangent_action k a v.val).symm.trans
        ((congrArg (fun z : (Fin s × Fin 3) → k => (M.geometricPeriodTangentEquiv k z).val)
          (funext (v.property a))).trans (M.geometricPeriodTangent_smul k _ v.val))⟩
  invFun t := ⟨(M.geometricPeriodTangentEquiv k).symm
      ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩, by
    intro a i
    let v := (M.geometricPeriodTangentEquiv k).symm
      ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩
    have ht := congrArg (fun z : RepresentationTheory.Theta.Geometric.TangentSources.extendedSchemeTangentPoints ℂ k M.abelian.toOver
      (RepresentationTheory.Theta.Geometric.ExtendedComplexPoints.extendedComplexPoint k 1) => z.val)
      ((M.geometricPeriodTangentEquiv k).apply_symm_apply
        ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩)
    have he : RepresentationTheory.Theta.Geometric.DiagonalExtension.diagonalOperator
        (fun p => (algebraMap ℂ k).comp (P.integralCharacters p)) a v =
        AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k τ a • v := by
      apply (M.geometricPeriodTangentEquiv k).injective
      apply Subtype.ext
      exact (M.geometricPeriodTangent_action k a v).trans
        ((congrArg (fun z : RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualTest ℂ k ⟶ M.abelian.toOver => z ≫ M.integralAction.map a)
          ht).trans ((t.property.2 a).trans
          ((congrArg (fun z : RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualTest ℂ k ⟶ M.abelian.toOver =>
            RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ k (AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k τ a) ≫ z) ht.symm).trans
            (M.geometricPeriodTangent_smul k _ v).symm)))
    exact congrFun he i⟩
  left_inv v := Subtype.ext ((M.geometricPeriodTangentEquiv k).symm_apply_apply v.val)
  right_inv t := Subtype.ext (congrArg (fun z : RepresentationTheory.Theta.Geometric.TangentSources.extendedSchemeTangentPoints ℂ k M.abelian.toOver
      (RepresentationTheory.Theta.Geometric.ExtendedComplexPoints.extendedComplexPoint k 1) => z.val)
    ((M.geometricPeriodTangentEquiv k).apply_symm_apply
      ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricLieEquiv_add (v w : AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal (P := P) k τ) :
    (M.geometricLieEquiv k τ (v + w)).val =
      (M.geometricLieEquiv k τ v).val * (M.geometricLieEquiv k τ w).val :=
  M.geometricPeriodTangent_add k v.val w.val

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricLieEquiv_smul (c : k) (v : AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal (P := P) k τ) :
    (M.geometricLieEquiv k τ (c • v)).val =
      RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ k c ≫ (M.geometricLieEquiv k τ v).val :=
  M.geometricPeriodTangent_smul k c v.val

omit M τ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal_finrank (hP : P.IsAdmissible) (σ : E ≃ₐ[ℚ] E) :
    Module.finrank k (AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal (P := P) k (P.μ.comp σ.toRingHom)) =
      P.lieRank σ := by
  change Module.finrank k (RepresentationTheory.Theta.Geometric.DiagonalEigen.diagonalEigenSpace
    (fun p => (algebraMap ℂ k).comp (P.integralCharacters p))
    ((algebraMap ℂ k).comp ((P.μ.comp σ.toRingHom).comp
      (algebraMap (NumberField.RingOfIntegers E) E)))) = _
  rw [RepresentationTheory.Theta.Geometric.DiagonalExtension.extendedDiagonal_finrank]
  have hc : Fintype.card {p : Fin s × Fin 3 // P.integralCharacters p =
      (P.μ.comp σ.toRingHom).comp (algebraMap (NumberField.RingOfIntegers E) E)} =
    Fintype.card {p : Fin s × Fin 3 // P.quotientCharacter p.1 p.2 =
      P.μ.comp σ.toRingHom} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun p => ⟨fun h =>
      IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers E)
        (fun a => congrArg (fun f : NumberField.RingOfIntegers E →+* ℂ => f a) h),
      fun h => congrArg (fun f : E →+* ℂ => f.comp (algebraMap (NumberField.RingOfIntegers E) E)) h⟩)
  rw [hc, P.quotientCharacter_count hP]
  rfl

omit τ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.hasGeometricLieRank (σ : E ≃ₐ[ℚ] E) :
    LieRanks.HasLieRank (M.abelianScheme.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ k))
      (M.integralAction.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ k))
      (AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k (P.μ.comp σ.toRingHom))
      (P.lieRank σ) := by
  let τ := P.μ.comp σ.toRingHom
  let b := (Module.finBasis k (AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal (P := P) k τ)).reindex
    (finCongr (AlgebraicModel.ReferenceAlgebraicModel.geometricDiagonal_finrank (P := P) k hP σ))
  let e := b.equivFun.symm
  apply RepresentationTheory.Theta.Geometric.LieFieldTests.hasLieRank_of_extended ℂ k M.abelianScheme M.integralAction (AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k τ)
    (P.lieRank σ) (e.toEquiv.trans (M.geometricLieEquiv k τ))
  · intro v w
    change (M.geometricLieEquiv k τ (e (v + w))).val = _
    rw [map_add, M.geometricLieEquiv_add]
    rfl
  · intro c v
    change (M.geometricLieEquiv k τ (e (c • v))).val = _
    rw [map_smul, M.geometricLieEquiv_smul]
    rfl

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GeometricLieRank.ReferenceAlgebraicModel

end

end OAI
