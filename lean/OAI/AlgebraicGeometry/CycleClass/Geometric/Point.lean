import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel

/-! # Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.Point.Cycles

noncomputable section

/-!+# The integral local class of a point

This file proves the dimension-zero normalization using actual relative singular
chains. It identifies the relative chain complex of `(X, ∅)` with the absolute
one, then uses the canonical zeroth-homology augmentation. Its distinguished
point class is the inverse image of `1: ℤ`, not an assumed fundamental class.
No positive-dimensional orientation or fundamental-class theorem is asserted.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

/-- An empty topological space has zero integral singular chain complex. -/
theorem integralSingularChains_isZero_of_isEmpty (X : TopCat.{0}) [IsEmpty X] :
    IsZero (LocalHomology.Cycles.integralSingularChains X) := by
  have hs : IsZero (∐ fun _ : X ↦ ModuleCat.of ℤ ℤ) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro x
    exact isEmptyElim x
  have hc : IsZero (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ ModuleCat.of ℤ ℤ)) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro n
    exact hs.eq_zero_of_src _
  exact hc.of_iso
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) X)

/-- The singular-chain inclusion from the empty subspace is the zero chain map. -/
theorem subspaceChainInclusion_empty (X : TopCat.{0}) :
    LocalHomology.Cycles.subspaceChainInclusion X ∅ = 0 :=
  (integralSingularChains_isZero_of_isEmpty (TopCat.of (∅ : Set X))).eq_zero_of_src _

/-- Quotienting integral singular chains by the chains of the empty subspace
does not change the chain complex. -/
def relativeEmptyChainsIso (X : TopCat.{0}) :
    LocalHomology.Cycles.relativeSingularChains X ∅ ≅ LocalHomology.Cycles.integralSingularChains X := by
  letI : IsIso (LocalHomology.Cycles.relativeChainProjection X ∅) :=
    cokernel.π_of_zero (subspaceChainInclusion_empty X)
  exact (asIso (LocalHomology.Cycles.relativeChainProjection X ∅)).symm

/-- Relative homology for the empty subspace is ordinary integral singular homology. -/
def relativeEmptyHomologyIso (X : TopCat.{0}) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X ∅ n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (relativeEmptyChainsIso X)

/-- On a path-connected space, the genuine relative group `H₀(X, ∅; ℤ)` is
identified with `ℤ` by the canonical augmentation. -/
def relativeEmptyHomologyZeroIso (X : TopCat.{0}) [PathConnectedSpace X] :
    LocalHomology.Cycles.relativeSingularHomology X ∅ 0 ≅ ModuleCat.of ℤ ℤ :=
  relativeEmptyHomologyIso X 0 ≪≫ ContractibleModel.Cycles.integralSingularH0Iso X

/-- The one-point topological model of a complex manifold of dimension zero. -/
abbrev pointModel : TopCat.{0} := TopCat.of PUnit

instance pointModel_pathConnectedSpace : PathConnectedSpace pointModel where
  nonempty := ⟨PUnit.unit⟩
  joined x y := by
    have h : x = y := Subsingleton.elim _ _
    subst y
    exact ⟨Path.refl x⟩

/-- The complement of the point in the one-point model is empty. -/
theorem pointModel_punctured_eq_empty :
    ({PUnit.unit}ᶜ : Set pointModel) = ∅ := by
  ext x
  simp

/-- The actual degree-zero local singular homology group of a point is `ℤ`. -/
def pointLocalHomologyZeroIso :
    LocalHomology.Cycles.localSingularHomology pointModel PUnit.unit 0 ≅ ModuleCat.of ℤ ℤ := by
  unfold LocalHomology.Cycles.localSingularHomology
  rw [pointModel_punctured_eq_empty]
  exact relativeEmptyHomologyZeroIso pointModel

/-- The positively normalized integral local class of the point. -/
def pointLocalClass : LocalHomology.Cycles.localSingularHomology pointModel PUnit.unit 0 :=
  pointLocalHomologyZeroIso.inv (1 : ℤ)

/-- The point class has augmentation exactly one. -/
@[simp]
theorem pointLocalClass_normalization :
    pointLocalHomologyZeroIso.hom pointLocalClass = 1 := by
  change (pointLocalHomologyZeroIso.inv ≫ pointLocalHomologyZeroIso.hom) (1 : ℤ) = 1
  simp

/-- The local class of the point is nonzero. -/
theorem pointLocalClass_ne_zero : pointLocalClass ≠ 0 := by
  intro h
  have hn := pointLocalClass_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every integral local class of a point is a unique integer multiple of its
positively normalized generator. -/
theorem pointLocalClass_generates
    (x : LocalHomology.Cycles.localSingularHomology pointModel PUnit.unit 0) :
    ∃! n : ℤ, n • pointLocalClass = x := by
  have hnorm (n : ℤ) : pointLocalHomologyZeroIso.hom (n • pointLocalClass) = n := by
    calc
      pointLocalHomologyZeroIso.hom (n • pointLocalClass) =
          n • (pointLocalHomologyZeroIso.hom pointLocalClass) :=
        map_zsmul pointLocalHomologyZeroIso.hom.hom _ _
      _ = n := by rw [pointLocalClass_normalization]; simp
  refine ⟨pointLocalHomologyZeroIso.hom x, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso pointLocalHomologyZeroIso.hom).1
    exact hnorm _
  · intro n hn
    calc
      n = pointLocalHomologyZeroIso.hom (n • pointLocalClass) := (hnorm n).symm
      _ = pointLocalHomologyZeroIso.hom x := congrArg pointLocalHomologyZeroIso.hom hn

/-- The genuine complex coordinate model in dimension zero is the point model. -/
def complexZeroModelHomeomorphPoint : (Fin 0 → ℂ) ≃ₜ pointModel where
  toFun _ := PUnit.unit
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The actual local homology normalization of the zero-dimensional complex
coordinate model, transported by its canonical homeomorphism with a point. -/
def complexZeroLocalHomologyIso :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 0 ≅ ModuleCat.of ℤ ℤ :=
  LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of (Fin 0 → ℂ)) (Y := pointModel)
    complexZeroModelHomeomorphPoint 0 0 ≪≫ pointLocalHomologyZeroIso

/-- The positively normalized local class in complex dimension zero. -/
def complexZeroLocalClass : LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 0 :=
  complexZeroLocalHomologyIso.inv (1 : ℤ)

@[simp]
theorem complexZeroLocalClass_normalization :
    complexZeroLocalHomologyIso.hom complexZeroLocalClass = 1 := by
  change (complexZeroLocalHomologyIso.inv ≫ complexZeroLocalHomologyIso.hom) (1 : ℤ) = 1
  simp

theorem complexZeroLocalClass_ne_zero : complexZeroLocalClass ≠ 0 := by
  intro h
  have hn := complexZeroLocalClass_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- The zero-dimensional complex local homology group is freely generated
by its positively normalized class. -/
theorem complexZeroLocalClass_generates
    (x : LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 0) :
    ∃! n : ℤ, n • complexZeroLocalClass = x := by
  have hnorm (n : ℤ) : complexZeroLocalHomologyIso.hom (n • complexZeroLocalClass) = n := by
    calc
      complexZeroLocalHomologyIso.hom (n • complexZeroLocalClass) =
          n • (complexZeroLocalHomologyIso.hom complexZeroLocalClass) :=
        map_zsmul complexZeroLocalHomologyIso.hom.hom _ _
      _ = n := by rw [complexZeroLocalClass_normalization]; simp
  refine ⟨complexZeroLocalHomologyIso.hom x, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso complexZeroLocalHomologyIso.hom).1
    exact hnorm _
  · intro n hn
    calc
      n = complexZeroLocalHomologyIso.hom (n • complexZeroLocalClass) := (hnorm n).symm
      _ = complexZeroLocalHomologyIso.hom x := congrArg complexZeroLocalHomologyIso.hom hn

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.Point.Cycles
