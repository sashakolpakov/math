import OAI.Analysis.PDE.Variational.CoordinateWrap
import OAI.Analysis.PDE.Variational.CellIsometry

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

def periodicRepresentative {H : Type*} [NormedAddCommGroup H]
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (f : Lp H 2 (volume.restrict (Icc a b))) : CellCoordinates m→H :=
  f ∘ coordinateWrap J a (b-a)

theorem stronglyMeasurable_periodicRepresentative {H : Type*} [NormedAddCommGroup H]
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    StronglyMeasurable (periodicRepresentative J a b f) :=
  (Lp.stronglyMeasurable f).comp_measurable (measurable_coordinateWrap J a (b-a))

theorem periodicRepresentative_periodic {H : Type*} [NormedAddCommGroup H]
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hL : ∀ i∈J, a i<b i)
    (f : Lp H 2 (volume.restrict (Icc a b))) (z : J→ℤ) (x : CellCoordinates m) :
    periodicRepresentative J a b f (x+coordinatePeriodShift J (b-a) z)=
      periodicRepresentative J a b f x := by
  simp only [periodicRepresentative,Function.comp_apply,
    coordinateWrap_periodic J a (b-a) (fun i hi ↦ sub_pos.mpr (hL i hi))]

def periodicCellPullback {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i) :
    Lp H 2 (volume.restrict (Icc a b)) →L[ℝ] Lp H 2 (volume.restrict (Icc c d)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (coordinateWrap J a (b-a))
    (measurePreserving_coordinateWrap J a b c d hL hlen ha hb)).toContinuousLinearMap

theorem periodicCellPullback_ae {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    periodicCellPullback J a b c d hL hlen ha hb f =ᵐ[volume.restrict (Icc c d)]
      periodicRepresentative J a b f :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_coordinateWrap J a b c d hL hlen ha hb)

theorem periodicCellPullback_continuous {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (f : CellCoordinates m→H) (hf : Continuous f)
    (hp : ∀ z x, f (x+coordinatePeriodShift J (b-a) z)=f x) :
    periodicCellPullback J a b c d hL hlen ha hb (cellToL2 a b f hf)=cellToL2 c d f hf := by
  apply Lp.ext
  have hmap := measurePreserving_coordinateWrap J a b c d hL hlen ha hb
  filter_upwards [periodicCellPullback_ae J a b c d hL hlen ha hb (cellToL2 a b f hf),
    hmap.quasiMeasurePreserving.ae (memLp_continuous_cell a b hf).coeFn_toLp,
    (memLp_continuous_cell c d hf).coeFn_toLp] with x hx hy hz
  rw [hx]
  change cellToL2 c d f hf x=f x at hz
  rw [hz]
  change cellToL2 a b f hf (coordinateWrap J a (b-a) x)=f x
  change cellToL2 a b f hf (coordinateWrap J a (b-a) x)=f (coordinateWrap J a (b-a) x) at hy
  rw [hy,coordinateWrap_eq_add_shift,hp]

theorem periodicCellIsometry_gradient_pullback
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m))
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) :
    (periodicCellIsometry J a b c d hL hlen ha hb Ω u).val =
      periodicCellPullback J a b c d hL hlen ha hb u.val := by
  let T := periodicCellIsometry J a b c d hL hlen ha hb Ω
  let B := periodicCellPullback (H := CellVectors m) J a b c d hL hlen ha hb
  have heq := (denseRange_periodicTestEmbedding a b Ω (coordinatePeriodSet J (b-a))).equalizer
    (continuous_subtype_val.comp T.continuous) (B.continuous.comp continuous_subtype_val)
    (funext fun φ ↦ by
      simp only [Function.comp_apply]
      change (periodicCellIsometry J a b c d hL hlen ha hb Ω
        (periodicTestEmbedding a b Ω _ φ)).val = _
      rw [periodicCellIsometry_test]
      exact (periodicCellPullback_continuous J a b c d hL hlen ha hb
        (cellGradient φ) (continuous_cellGradient (periodicTest_contDiff_one φ))
        (fun z x ↦ cellGradient_periodic (φ.property.2.2 _ ⟨z,rfl⟩) x)).symm)
  exact congrFun heq u

theorem periodicCellIsometry_value_pullback
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hab : a≤b) (hcd : c≤d)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (hface' : ∀ y∈Icc (c∘k.succAbove) (d∘k.succAbove), k.insertNth (d k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) :
    periodicValue c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u) =
      periodicCellPullback J a b c d hL hlen ha hb (periodicValue a b Ω _ u) := by
  let T := periodicCellIsometry J a b c d hL hlen ha hb Ω
  let B := periodicCellPullback (H := ℝ) J a b c d hL hlen ha hb
  have heq := (denseRange_periodicTestEmbedding a b Ω (coordinatePeriodSet J (b-a))).equalizer
    ((periodicValue c d Ω _).continuous.comp T.continuous)
    (B.continuous.comp (periodicValue a b Ω _).continuous)
    (funext fun φ ↦ by
      simp only [Function.comp_apply]
      change periodicValue c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω
        (periodicTestEmbedding a b Ω _ φ)) = _
      rw [periodicCellIsometry_test,periodicValue_test c d hcd Ω _ k hface',
        periodicValue_test a b hab Ω _ k hface]
      exact (periodicCellPullback_continuous J a b c d hL hlen ha hb φ.val
        (periodicTest_contDiff φ).continuous (fun z x ↦ φ.property.2.2 _ ⟨z,rfl⟩ x)).symm)
  exact congrFun heq u

end OAI.Analysis.PDE.Variational
