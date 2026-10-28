import OAI.Analysis.Fourier.WavePackets.QuaternionPadding
import OAI.Analysis.PDE.Concentration.Packet.PeriodBasis
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Concentration

def fourthCoordinatesLinear (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 →ₗ[ℝ] (Fin m → ℝ) where
  toFun x i := x (i, Fin.last 3)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fourthCoordinates (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 →L[ℝ] (Fin m → ℝ) :=
  (fourthCoordinatesLinear m).toContinuousLinearMap

def fourthInjectionLinear (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 where
  toFun d := WithLp.toLp 2 (fun i => Fin.lastCases (d i.1) (fun _ => 0) i.2)
  map_add' d e := by
    ext ⟨i, a⟩
    change Fin.lastCases (motive := fun _ => ℝ) (d i + e i) (fun _ => 0) a =
      Fin.lastCases (motive := fun _ => ℝ) (d i) (fun _ => 0) a +
        Fin.lastCases (motive := fun _ => ℝ) (e i) (fun _ => 0) a
    refine Fin.lastCases ?_ (fun a => ?_) a <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, add_zero]
  map_smul' c d := by
    ext ⟨i, a⟩
    change Fin.lastCases (motive := fun _ => ℝ) (c * d i) (fun _ => 0) a =
      c * Fin.lastCases (motive := fun _ => ℝ) (d i) (fun _ => 0) a
    refine Fin.lastCases ?_ (fun a => ?_) a <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero]

def fourthInjection (m : ℕ) : (Fin m → ℝ) →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 :=
  (fourthInjectionLinear m).toContinuousLinearMap

@[simp] theorem fourthCoordinates_apply (m : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) (i : Fin m) :
    fourthCoordinates m x i = x (i, Fin.last 3) := rfl

@[simp] theorem fourthInjection_last (m : ℕ) (d : Fin m → ℝ) (i : Fin m) :
    fourthInjection m d (i, Fin.last 3) = d i := by
  change Fin.lastCases (motive := fun _ => ℝ) (d i) (fun _ => 0) (Fin.last 3) = d i
  exact Fin.lastCases_last

@[simp] theorem fourthInjection_castSucc (m : ℕ) (d : Fin m → ℝ) (i : Fin m) (a : Fin 3) :
    fourthInjection m d (i, a.castSucc) = 0 := by
  change Fin.lastCases (motive := fun _ => ℝ) (d i) (fun _ => 0) a.castSucc = 0
  exact Fin.lastCases_castSucc a

@[simp] theorem dropFourth_fourthInjection (m : ℕ) (d : Fin m → ℝ) :
    dropFourth m (fourthInjection m d) = 0 := by ext ⟨i,a⟩; simp

@[simp] theorem fourthCoordinates_insertFourth (m : ℕ) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) :
    fourthCoordinates m (insertFourth m y) = 0 := by
  ext i
  exact insertFourth_last m y i

@[simp] theorem fourthCoordinates_fourthInjection (m : ℕ) (d : Fin m → ℝ) :
    fourthCoordinates m (fourthInjection m d) = d := by
  ext i
  exact fourthInjection_last m d i

theorem insertFourth_dropFourth_add (m : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) :
    insertFourth m (dropFourth m x) + fourthInjection m (fourthCoordinates m x) = x := by
  ext ⟨i,a⟩
  refine Fin.lastCases ?_ (fun a => ?_) a <;>
    simp only [PiLp.add_apply, insertFourth_last, fourthInjection_last,
      fourthCoordinates_apply, zero_add, insertFourth_castSucc, fourthInjection_castSucc,
      dropFourth_apply, add_zero]

def fourthSplit (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 × (Fin m → ℝ) where
  toFun x := (dropFourth m x, fourthCoordinates m x)
  invFun p := insertFourth m p.1 + fourthInjection m p.2
  left_inv := insertFourth_dropFourth_add m
  right_inv p := by
    apply Prod.ext
    · simp only [map_add, dropFourth_insertFourth, dropFourth_fourthInjection, add_zero]
    · simp only [map_add, fourthCoordinates_insertFourth, fourthCoordinates_fourthInjection, zero_add]
  map_add' x y := by simp
  map_smul' c x := by simp
  continuous_toFun := (dropFourth m).continuous.prodMk (fourthCoordinates m).continuous
  continuous_invFun := ((insertFourth m).continuous.comp continuous_fst).add
    ((fourthInjection m).continuous.comp continuous_snd)

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Add the fourth slots to the periodic, not the transverse, coordinates. -/
def paddedLatticeSplit (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] (P × (Fin m → ℝ)) × V :=
  (fourthSplit m).trans ((e.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin m → ℝ))).trans
    ((ContinuousLinearEquiv.prodAssoc ℝ P V (Fin m → ℝ)).trans
    (((ContinuousLinearEquiv.refl ℝ P).prodCongr
      (ContinuousLinearEquiv.prodComm ℝ V (Fin m → ℝ))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ P (Fin m → ℝ) V).symm)))

theorem paddedLatticeSplit_apply (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) :
    paddedLatticeSplit e x = (((e (dropFourth m x)).1, fourthCoordinates m x),
      (e (dropFourth m x)).2) := rfl

theorem paddedLatticeSplit_symm (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V)
    (p : P) (d : Fin m → ℝ) (v : V) :
    (paddedLatticeSplit e).symm ((p,d),v) =
      insertFourth m (e.symm (p,v)) + fourthInjection m d := rfl

def paddedLatticeBasis (b : Basis ι ℝ P) : Basis (ι ⊕ Fin m) ℝ (P × (Fin m → ℝ)) :=
  b.prod (Pi.basisFun ℝ (Fin m))

omit [Fintype ι] in
theorem latticePeriodic_dropFourth {W : Type*} (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V)
    (b : Basis ι ℝ P) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 → W} (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (paddedLatticeSplit (m := m) (P := P) (V := V) e) (paddedLatticeBasis (m := m) b)
      (fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 => f (dropFourth m x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  rcases i with i | i
  · have hper := hf (dropFourth m x) ⟨b i, Submodule.subset_span (mem_range_self i)⟩
    have he : e.symm ((e (dropFourth m x)).1 + b i, (e (dropFourth m x)).2) =
        dropFourth m x + e.symm (b i, 0) := by
      apply e.injective
      simp only [ContinuousLinearEquiv.apply_symm_apply, map_add]
      apply Prod.ext <;> simp
    rw [he] at hper
    simpa only [paddedLatticeBasis, Basis.prod_apply, Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply,
      paddedLatticeSplit_symm, map_add, dropFourth_insertFourth,
      dropFourth_fourthInjection, add_zero] using hper
  · simp only [paddedLatticeBasis, Basis.prod_apply, Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      paddedLatticeSplit_symm, map_add, dropFourth_fourthInjection, add_zero, Prod.mk_zero_zero, map_zero]

end OAI.Analysis.Fourier.WavePackets
