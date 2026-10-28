import OAI.NumberTheory.Adeles.LocalNorms

/-! # Infinite Norm -/

namespace OAI.NumberTheory.Adeles.InfiniteNorm.CompletionFactors

noncomputable section

section

/-! Products of actual local extension norms at the infinite places. -/

open _root_.NumberField
open scoped _root_.NumberField _root_.Topology _root_.NumberField.LiesOver

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

abbrev InfinitePlacesOver (E : Type*) [Field E] [Algebra F E] (v : InfinitePlace F) :=
  {w : InfinitePlace E // w.LiesOver v}

instance infinitePlacesOver_liesOver (v : InfinitePlace F) (w : InfinitePlacesOver E v) :
    w.val.LiesOver v := w.property

instance infinitePlacesOver_fintype (v : InfinitePlace F) :
    Fintype (InfinitePlacesOver E v) := Fintype.ofFinite _

def infiniteNormCoordinate (v : InfinitePlace F) : InfiniteAdeleRing E →* v.Completion where
  toFun a := ∏ w : InfinitePlacesOver E v, LocalNorms.CompletionFactors.infiniteLocalNorm v w.val (a w.val)
  map_one' := by
    change (∏ w : InfinitePlacesOver E v, LocalNorms.CompletionFactors.infiniteLocalNorm v w.val 1) = 1
    simp
  map_mul' a b := by
    change (∏ w : InfinitePlacesOver E v, LocalNorms.CompletionFactors.infiniteLocalNorm v w.val (a w.val * b w.val)) = _
    simp only [map_mul, Finset.prod_mul_distrib]

omit [NumberField F] in
theorem continuous_infiniteNormCoordinate (v : InfinitePlace F) :
    Continuous (infiniteNormCoordinate (E := E) v) := by
  apply continuous_finsetProd
  intro w _
  have he : Continuous (fun a : InfiniteAdeleRing E => a w.val) := continuous_apply w.val
  exact (LocalNorms.CompletionFactors.continuous_infiniteLocalNorm v w.val).comp he

def infiniteAdeleNorm : InfiniteAdeleRing E →* InfiniteAdeleRing F where
  toFun a v := infiniteNormCoordinate v a
  map_one' := funext fun v => map_one (infiniteNormCoordinate v)
  map_mul' a b := funext fun v => map_mul (infiniteNormCoordinate v) a b

omit [NumberField F] in
theorem continuous_infiniteAdeleNorm : Continuous (infiniteAdeleNorm (F := F) (E := E)) :=
  continuous_pi fun v => continuous_infiniteNormCoordinate v

def infiniteIdeleNorm : (InfiniteAdeleRing E)ˣ →ₜ* (InfiniteAdeleRing F)ˣ where
  toMonoidHom := Units.map infiniteAdeleNorm
  continuous_toFun := Continuous.units_map _ continuous_infiniteAdeleNorm

end

/-! The completed scalar extension at an infinite place. -/

open _root_.NumberField
open scoped _root_.NumberField _root_.Topology TensorProduct _root_.NumberField.LiesOver

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]
  (v : InfinitePlace F)

instance infiniteCompletion_scalarTower (w : InfinitePlace E) : IsScalarTower F E w.Completion :=
  .of_algebraMap_eq fun _ => rfl

abbrev InfiniteBlock := (w : InfinitePlacesOver E v) → w.val.Completion

def infiniteTensorMap : v.Completion ⊗[F] E →ₐ[v.Completion] InfiniteBlock (E := E) v :=
  Algebra.TensorProduct.lift
    (Algebra.algHom v.Completion v.Completion (InfiniteBlock (E := E) v))
    (Algebra.algHom F E (InfiniteBlock (E := E) v)) (fun _ _ => mul_comm ..)

omit [NumberField F] in
theorem infiniteBlock_denseRange :
    DenseRange (algebraMap E (InfiniteBlock (E := E) v)) := by
  classical
  let p : InfiniteAdeleRing E → InfiniteBlock (E := E) v := fun a w => a w.val
  have hp : Continuous p := continuous_pi fun w => continuous_apply w.val
  have hs : Function.Surjective p := by
    intro a
    refine ⟨fun w => if h : w.LiesOver v then a ⟨w, h⟩ else 0, ?_⟩
    funext w
    simp [p, w.property]
  exact hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hp

theorem infiniteTensorMap_surjective : Function.Surjective (infiniteTensorMap (E := E) v) := by
  let := LocalNorms.CompletionFactors.infiniteCompletionNontriviallyNormedField v
  have hd : DenseRange (infiniteTensorMap (E := E) v) := by
    apply (infiniteBlock_denseRange (E := E) v).mono
    rintro _ ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ[F] x, ?_⟩
    simp [infiniteTensorMap, Algebra.algHom]
  change Function.Surjective (infiniteTensorMap (E := E) v).toLinearMap
  rw [← Set.range_eq_univ, ← (infiniteTensorMap (E := E) v).toLinearMap.coe_range,
    ← (infiniteTensorMap (E := E) v).toLinearMap.range.closed_of_finiteDimensional.closure_eq]
  exact hd.closure_range

instance infiniteBlock_finiteDimensional :
    FiniteDimensional v.Completion (InfiniteBlock (E := E) v) := by
  let : ∀ w : InfinitePlacesOver E v, FiniteDimensional v.Completion w.val.Completion :=
    fun w => LocalNorms.CompletionFactors.infiniteCompletion_finiteDimensional v w.val
  infer_instance

theorem infiniteBlock_finrank :
    Module.finrank v.Completion (InfiniteBlock (E := E) v) = Module.finrank F E := by
  classical
  let : ∀ w : InfinitePlacesOver E v, FiniteDimensional v.Completion w.val.Completion :=
    fun w => LocalNorms.CompletionFactors.infiniteCompletion_finiteDimensional v w.val
  rw [Module.finrank_pi_fintype]
  have h := InfinitePlace.sum_inertiaDeg_eq_finrank F E v
  rw [Finset.sum_subtype (p := fun w : InfinitePlace E => w.LiesOver v)
    (v.placesOver E).toFinset (by intro x; exact Set.mem_toFinset)
    (fun w => v.inertiaDeg w)] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro w _
  exact (v.inertiaDeg_eq_finrank w.val).symm

/-- The scalar extension at an infinite place is the product of its local extensions. -/
def infiniteTensorEquiv : v.Completion ⊗[F] E ≃ₐ[v.Completion] InfiniteBlock (E := E) v :=
  AlgEquiv.ofBijective (infiniteTensorMap v) (by
    have hd : Module.finrank v.Completion (v.Completion ⊗[F] E) =
        Module.finrank v.Completion (InfiniteBlock (E := E) v) := by
      rw [Module.finrank_baseChange, infiniteBlock_finrank]
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
      (infiniteTensorMap_surjective v), infiniteTensorMap_surjective v⟩)

end

end OAI.NumberTheory.Adeles.InfiniteNorm.CompletionFactors
