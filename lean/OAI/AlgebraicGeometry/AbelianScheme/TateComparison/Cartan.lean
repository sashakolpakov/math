import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

/-! # Cartan -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cartan

noncomputable section

/-! The GL3 Cartan decomposition constructed from the supplied ElementaryDivisors
elementary-divisor theorem. Integral basis changes are proved integral
from equality of their lattice spans. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

abbrev LocalBasis := Module.Basis (Fin 3) ℚ_[q] (Fin 3 → ℚ_[q])

def basisTransition (e f : LocalBasis q) : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] where
  val := e.toMatrix f
  inv := f.toMatrix e
  val_inv := e.toMatrix_mul_toMatrix_flip f
  inv_val := f.toMatrix_mul_toMatrix_flip e

theorem basisTransition_mul (e f b : LocalBasis q) :
    basisTransition q e f * basisTransition q f b = basisTransition q e b := by
  apply Units.ext
  exact e.toMatrix_mul_toMatrix f b

theorem basisMatrix_integral (e f : LocalBasis q)
    (h : Submodule.span ℤ_[q] (Set.range e) = Submodule.span ℤ_[q] (Set.range f)) :
    e.toMatrix f ∈ MonoidHom.mrange (CentralConvolution.padicMatrixInclusion q).toMonoidHom := by
  have hc : ∀ i j : Fin 3, ∃ r : ℤ_[q], (r : ℚ_[q]) = e.toMatrix f i j := by
    intro i j
    apply (e.mem_span_iff_repr_mem ℤ_[q] (f j)).mp _ i
    rw [h]
    exact Submodule.subset_span (Set.mem_range_self j)
  choose r hr using hc
  refine ⟨r, ?_⟩
  ext i j
  exact hr i j

theorem basisTransition_integral (e f : LocalBasis q)
    (h : Submodule.span ℤ_[q] (Set.range e) = Submodule.span ℤ_[q] (Set.range f)) :
    basisTransition q e f ∈ (Matrix.GeneralLinearGroup.map (n := Fin 3)
      (PadicInt.Coe.ringHom (p := q))).range := by
  change basisTransition q e f ∈ (Units.map (CentralConvolution.padicMatrixInclusion q).toMonoidHom).range
  rw [CentralConvolution.unitsMap_range _ (CentralConvolution.padicMatrixInclusion_isOpenEmbedding q).injective]
  exact ⟨basisMatrix_integral q e f h, basisMatrix_integral q f e h.symm⟩

abbrev standardLocalBasis : LocalBasis q := Pi.basisFun ℚ_[q] (Fin 3)

def matrixLocalBasis (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) : LocalBasis q :=
  (standardLocalBasis q).map (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv

theorem basisTransition_matrixLocalBasis (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    basisTransition q (standardLocalBasis q) (matrixLocalBasis q g) = g := by
  apply Units.ext
  ext i j
  change (standardLocalBasis q).repr ((matrixLocalBasis q g) j) i = g.val i j
  simp [standardLocalBasis, matrixLocalBasis]

def scaledLocalBasis (e : LocalBasis q) (a : Fin 3 → ℤ) : LocalBasis q :=
  e.unitsSMul (fun i => HeckeKernel.qUnit q ^ a i)

theorem scaledLocalBasis_apply (e : LocalBasis q) (a : Fin 3 → ℤ) (i : Fin 3) :
    scaledLocalBasis q e a i = (q : ℚ_[q]) ^ a i • e i := by
  simp only [scaledLocalBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Units.val_zpow_eq_zpow_val, HeckeKernel.qUnit, Units.val_mk0]

theorem basisTransition_scaled (e : LocalBasis q) (a : Fin 3 → ℤ) :
    basisTransition q e (scaledLocalBasis q e a) = HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i) := by
  apply Units.ext
  exact e.toMatrix_unitsSMul _

/-- ElementaryDivisors gives integral left and right changes of basis and a dominant
diagonal representative. Applying ElementaryDivisors to g^-1 makes the exponents -a
dominant, matching the inverse-representative superlattice convention. -/
theorem exists_GL3_cartan (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    ∃ a : Fin 3 → ℤ, Antitone a ∧
      ∃ l r : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q],
        g = Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) l *
          HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i) *
          Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) r := by
  let b₀ := standardLocalBasis q
  let b₁ := matrixLocalBasis q g⁻¹
  obtain ⟨a, ⟨ha, e, h₀, h₁⟩, _⟩ := hElementaryDivisors (q : ℤ_[q]) PadicInt.irreducible_p
    (Duality.latticeOfBasis (R := ℤ_[q]) b₀).val (Duality.latticeOfBasis (R := ℤ_[q]) b₁).val
    (Duality.latticeOfBasis (R := ℤ_[q]) b₀).property (Duality.latticeOfBasis (R := ℤ_[q]) b₁).property
  have hscaled : Submodule.span ℤ_[q] (Set.range (scaledLocalBasis q e a)) =
      Submodule.span ℤ_[q] (Set.range b₁) := by
    rw [show Submodule.span ℤ_[q] (Set.range b₁) = _ from h₁]
    congr 1
    congr 1
    funext i
    rw [scaledLocalBasis_apply]
    simp only [map_natCast]
  obtain ⟨l, hl⟩ := basisTransition_integral q b₀ e h₀
  obtain ⟨r, hr⟩ := basisTransition_integral q (scaledLocalBasis q e a) b₁ hscaled
  have hg : Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) l *
      HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i) *
      Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) r = g⁻¹ := by
    rw [hl, hr, ← basisTransition_scaled, basisTransition_mul, basisTransition_mul]
    exact basisTransition_matrixLocalBasis q g⁻¹
  refine ⟨fun i => -a i, fun i j hij => neg_le_neg (ha hij), r⁻¹, l⁻¹, ?_⟩
  have hinv := congrArg Inv.inv hg
  have hd : (HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i))⁻¹ =
      HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ (-a i)) := by
    change (CentralConvolution.diagonalHom (fun i => HeckeKernel.qUnit q ^ a i))⁻¹ = CentralConvolution.diagonalHom _
    rw [← map_inv]
    congr 1
    funext i
    exact (zpow_neg _ _).symm
  simpa only [mul_inv_rev, map_inv, hd, inv_inv, mul_assoc] using hinv.symm

/-- A nonzero q-adic scalar is an integral unit times a power of q. -/
theorem exists_scalar_cartan (x : ℚ_[q]ˣ) :
    ∃ (h : ℤ) (u : ℤ_[q]ˣ),
      x = Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom u * HeckeKernel.qUnit q ^ h := by
  let h := x.val.valuation
  have hq : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hnorm : ‖x.val * (q : ℚ_[q]) ^ (-h)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, Padic.norm_p_zpow, neg_neg]
    change (q : ℝ) ^ (-h) * (q : ℝ) ^ h = 1
    rw [← zpow_add₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero),
      neg_add_cancel, zpow_zero]
  refine ⟨h, PadicInt.mkUnits hnorm, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val]
  change x.val = (x.val * (q : ℚ_[q]) ^ (-h)) * (q : ℚ_[q]) ^ h
  rw [mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one]

/-- Cartan decomposition of the entire split similitude group, with its
single shared multiplier. Both remaining factors lie in the actual level. -/
theorem exists_split_cartan (s : ℕ) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (g : HeckeKernel.SplitGroup s q) :
    ∃ t : Local.LocalType s, ∃ l r : HeckeKernel.integralLevel s q,
      g = (l : HeckeKernel.SplitGroup s q) * HeckeKernel.representative s q t * (r : HeckeKernel.SplitGroup s q) := by
  choose a ha using fun v : Fin s => exists_GL3_cartan q hElementaryDivisors (g.1 v)
  choose l r hlr using fun v => (ha v).2
  obtain ⟨h, u, hu⟩ := exists_scalar_cartan q g.2
  let t : Local.LocalType s := ⟨h, a, fun v => (ha v).1⟩
  let l' : HeckeKernel.integralLevel s q := ⟨HeckeKernel.integralLevelMap s q (l, u), ⟨(l, u), rfl⟩⟩
  let r' : HeckeKernel.integralLevel s q := ⟨HeckeKernel.integralLevelMap s q (r, 1), ⟨(r, 1), rfl⟩⟩
  refine ⟨t, l', r', Prod.ext ?_ ?_⟩
  · funext v
    exact hlr v
  · change g.2 = (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom u *
      HeckeKernel.qUnit q ^ h) * Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom 1
    rw [map_one, mul_one]
    exact hu

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cartan
