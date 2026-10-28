import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexLowerSupport
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativeBoundary
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSupport

/-! # Double Complex Map Reduction -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapReduction.DoubleComplex

noncomputable section

/-!
# Removing the first occupied column of a relative total cocycle

The argument uses actual component projections of the total complexes.
Column quasi-isomorphisms supply relative primitives, and the tensor sign
specifies their inclusion into the total complex.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  {K L : HomologicalComplex₂ (ModuleCat.{v} R)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)}

/-- Totalizing a bicomplex map does not decrease horizontal support. -/
theorem _root_.OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexLowerSupport.DoubleComplex.SupportedFrom.total_map (φ : K ⟶ L) {n m : ℕ}
    {x : (K.total (ComplexShape.up ℕ)).X n} (hx : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K n m x) :
    DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n m ((HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n x) := by
  intro p q hpq hp
  rw [DoubleComplexMapComponents.DoubleComplex.project_total_map, hx p q hpq hp, map_zero]

/-- The first occupied component of a total cocycle is a vertical cocycle. -/
theorem lowest_component_closed
    (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (n p q : ℕ) (hpq : p + q = n) (x : (K.total (ComplexShape.up ℕ)).X n)
    (hxs : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K n p x)
    (hx : (K.total (ComplexShape.up ℕ)).d n (n + 1) x = 0) :
    (K.X p).d q (q + 1) (DoubleComplexProjections.DoubleComplex.πTotal K p q n hpq x) = 0 := by
  have h := DoubleComplexLowerSupport.DoubleComplex.project_d_of_supportedFrom K p q n hpq x hxs
  rw [hx, map_zero] at h
  exact (DoubleComplexRelativeBoundary.DoubleComplex.sign_zsmul_eq_zero_iff p _).mp h.symm

private theorem included_vertical_component
    (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q i j : ℕ) (h : p + q = i) (hj : i + 1 = j) (c : (K.X p).X q) :
    DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) j (by omega)
        ((K.total (ComplexShape.up ℕ)).d i j (K.ιTotal (ComplexShape.up ℕ) p q i h c)) =
      ((-1 : ℤ) ^ p) • (K.X p).d q (q + 1) c := by
  subst j
  exact DoubleComplexDifferential.DoubleComplex.project_d_iota_vertical K p q i h c

private theorem included_d_supported
    (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q i j : ℕ) (h : p + q = i) (hj : i + 1 = j) (c : (K.X p).X q) :
    DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K j p
      ((K.total (ComplexShape.up ℕ)).d i j (K.ιTotal (ComplexShape.up ℕ) p q i h c)) := by
  subst j
  exact DoubleComplexLowerSupport.DoubleComplex.supportedFrom_d_iota K p q i h c

variable (φ : K ⟶ L)

/-- Projecting a relative cycle into its first occupied column produces a
relative cycle of that column map, after applying the totalization sign. -/
theorem column_relative_primitive (hφ : ∀ p : ℕ, QuasiIso (φ.f p))
    (n m r : ℕ) (hmr : m + r = n)
    (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (y : (L.total (ComplexShape.up ℕ)).X n)
    (hxs : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) m x) (hys : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n m y)
    (hx : (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hxy : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f (n + 1) x =
      (L.total (ComplexShape.up ℕ)).d n (n + 1) y) :
    ∃ c : (K.X m).X r,
      (K.X m).d r (r + 1) c = DoubleComplexProjections.DoubleComplex.πTotal K m (r + 1) (n + 1) (by omega) x ∧
      ∃ e : (L.X m).X r.pred,
        ((-1 : ℤ) ^ m) • DoubleComplexProjections.DoubleComplex.πTotal L m r n hmr y =
          (φ.f m).f r c - (L.X m).d r.pred r e := by
  have ha := lowest_component_closed K (n + 1) m (r + 1) (by omega) x hxs hx
  have hab := congrArg (DoubleComplexProjections.DoubleComplex.πTotal L m (r + 1) (n + 1) (by omega)) hxy
  rw [DoubleComplexMapComponents.DoubleComplex.project_total_map, DoubleComplexLowerSupport.DoubleComplex.project_d_of_supportedFrom L m r n hmr y hys] at hab
  have hab' : (φ.f m).f (r + 1) (DoubleComplexProjections.DoubleComplex.πTotal K m (r + 1) (n + 1) (by omega) x) =
      (L.X m).d r (r + 1) (((-1 : ℤ) ^ m) • DoubleComplexProjections.DoubleComplex.πTotal L m r n hmr y) := by
    simpa only [map_zsmul] using hab
  exact DoubleComplexRelativePrimitive.DoubleComplex.relative_primitive_succ (φ.f m) (hφ m) r
    (DoubleComplexProjections.DoubleComplex.πTotal K m (r + 1) (n + 1) (by omega) x)
    (((-1 : ℤ) ^ m) • DoubleComplexProjections.DoubleComplex.πTotal L m r n hmr y) ha hab'

/-- Once only the last possible horizontal column remains, a relative cycle
vanishes by injectivity on degree-zero column cohomology. -/
theorem relative_supported_last_zero (hφ : ∀ p : ℕ, QuasiIso (φ.f p))
    (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (y : (L.total (ComplexShape.up ℕ)).X n)
    (hxs : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) (n + 1) x) (hys : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n (n + 1) y)
    (hx : (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hxy : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f (n + 1) x =
      (L.total (ComplexShape.up ℕ)).d n (n + 1) y) : x = 0 ∧ y = 0 := by
  have hy0 : y = 0 := by
    apply DoubleComplexProjections.DoubleComplex.total_element_ext L n
    intro p q hpq
    rw [map_zero]
    exact hys p q hpq (by omega)
  have ha := lowest_component_closed K (n + 1) (n + 1) 0 (by omega) x hxs hx
  have hfa := congrArg (DoubleComplexProjections.DoubleComplex.πTotal L (n + 1) 0 (n + 1) (by omega)) hxy
  rw [DoubleComplexMapComponents.DoubleComplex.project_total_map, hy0, map_zero, map_zero] at hfa
  have ha0 := DoubleComplexRelativePrimitive.DoubleComplex.relative_cycle_zero (φ.f (n + 1)) (hφ (n + 1))
    (DoubleComplexProjections.DoubleComplex.πTotal K (n + 1) 0 (n + 1) (by omega) x) ha hfa
  refine ⟨?_, hy0⟩
  apply DoubleComplexProjections.DoubleComplex.total_element_ext K (n + 1)
  intro p q hpq
  rw [map_zero]
  by_cases hp : p < n + 1
  · exact hxs p q hpq hp
  · have hp' : p = n + 1 := by omega
    subst p
    have hq : q = 0 := by omega
    subst q
    exact ha0

/-- The degree-zero relative kernel of the total map is trivial. -/
theorem total_relative_cycle_zero (hφ : ∀ p : ℕ, QuasiIso (φ.f p))
    (x : (K.total (ComplexShape.up ℕ)).X 0)
    (hx : (K.total (ComplexShape.up ℕ)).d 0 1 x = 0)
    (hfx : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f 0 x = 0) : x = 0 := by
  have ha := lowest_component_closed K 0 0 0 rfl x (DoubleComplexLowerSupport.DoubleComplex.supportedFrom_zero_degree K 0 x) hx
  have hfa := congrArg (DoubleComplexProjections.DoubleComplex.πTotal L 0 0 0 rfl) hfx
  rw [DoubleComplexMapComponents.DoubleComplex.project_total_map, map_zero] at hfa
  have ha0 := DoubleComplexRelativePrimitive.DoubleComplex.relative_cycle_zero (φ.f 0) (hφ 0) (DoubleComplexProjections.DoubleComplex.πTotal K 0 0 0 rfl x) ha hfa
  apply DoubleComplexProjections.DoubleComplex.total_element_ext K 0
  intro p q hpq
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst p
  subst q
  rw [map_zero]
  exact ha0

/-- Subtracting the signed inclusion of a column relative primitive removes
the first occupied column from both members of the total relative cycle. -/
theorem raise_relative_support (hφ : ∀ p : ℕ, QuasiIso (φ.f p))
    (n m r : ℕ) (hmr : m + r = n)
    (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (y : (L.total (ComplexShape.up ℕ)).X n)
    (hxs : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) m x) (hys : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n m y)
    (hx : (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hxy : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f (n + 1) x =
      (L.total (ComplexShape.up ℕ)).d n (n + 1) y) :
    ∃ a : (K.total (ComplexShape.up ℕ)).X n,
      ∃ b : (L.total (ComplexShape.up ℕ)).X n.pred,
        DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) (m + 1) (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) a) ∧
          DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n (m + 1)
            (y - (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n a +
              (L.total (ComplexShape.up ℕ)).d n.pred n b) := by
  obtain ⟨c, hc, e, he⟩ := column_relative_primitive φ hφ n m r hmr x y hxs hys hx hxy
  let a := K.ιTotal (ComplexShape.up ℕ) m r n hmr (((-1 : ℤ) ^ m) • c)
  have ha : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) m ((K.total (ComplexShape.up ℕ)).d n (n + 1) a) :=
    DoubleComplexLowerSupport.DoubleComplex.supportedFrom_d_iota K m r n hmr (((-1 : ℤ) ^ m) • c)
  have hfa : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n m ((HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n a) :=
    DoubleComplexLowerSupport.DoubleComplex.SupportedFrom.total_map φ (DoubleComplexLowerSupport.DoubleComplex.supportedFrom_iota K m r n hmr (((-1 : ℤ) ^ m) • c))
  have hpa : DoubleComplexProjections.DoubleComplex.πTotal L m r n hmr ((HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n a) =
      ((-1 : ℤ) ^ m) • (φ.f m).f r c := by
    dsimp only [a]
    rw [DoubleComplexMapComponents.DoubleComplex.project_total_map, DoubleComplexSupport.DoubleComplex.project_iota_self, map_zsmul]
  have hx' : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) (m + 1)
      (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) a) := by
    intro p q hpq hp
    rw [map_sub]
    by_cases hpm : p < m
    · rw [hxs p q hpq hpm, ha p q hpq hpm, sub_zero]
    · have hp' : p = m := by omega
      subst p
      have hq : q = r + 1 := by omega
      subst q
      dsimp only [a]
      rw [DoubleComplexDifferential.DoubleComplex.project_d_iota_vertical, map_zsmul]
      have hs := DoubleComplexRelativeBoundary.DoubleComplex.sign_zsmul_involutive m ((K.X m).d r (r + 1) c)
      change ((-1 : ℤ) ^ m) • (((-1 : ℤ) ^ m) • (K.X m).d r (r + 1) c) =
        (K.X m).d r (r + 1) c at hs
      rw [hs, hc, sub_self]
  cases r with
  | zero =>
    have hshape : (L.X m).d 0 0 = 0 := (L.X m).shape 0 0 (by decide)
    change ((-1 : ℤ) ^ m) • DoubleComplexProjections.DoubleComplex.πTotal L m 0 n hmr y = (φ.f m).f 0 c - (L.X m).d 0 0 e at he
    rw [hshape] at he
    change ((-1 : ℤ) ^ m) • DoubleComplexProjections.DoubleComplex.πTotal L m 0 n hmr y = (φ.f m).f 0 c - 0 at he
    rw [sub_zero] at he
    have hb : DoubleComplexProjections.DoubleComplex.πTotal L m 0 n hmr y = ((-1 : ℤ) ^ m) • (φ.f m).f 0 c :=
      (DoubleComplexRelativeBoundary.DoubleComplex.sign_zsmul_involutive m _).symm.trans
        (congrArg (fun z => ((-1 : ℤ) ^ m) • z) he)
    refine ⟨a, 0, hx', ?_⟩
    intro p q hpq hp
    simp only [map_zero, add_zero, map_sub]
    by_cases hpm : p < m
    · rw [hys p q hpq hpm, hfa p q hpq hpm, sub_zero]
    · have hp' : p = m := by omega
      subst p
      have hq : q = 0 := by omega
      subst q
      rw [hpa, hb, sub_self]
  | succ r =>
    have hn : n = (m + r) + 1 := by omega
    have hmr' : m + r = n.pred := by rw [hn]; rfl
    have hn' : n.pred + 1 = n := by rw [← hmr']; exact hn.symm
    let b := L.ιTotal (ComplexShape.up ℕ) m r n.pred hmr' e
    have hb : DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n m ((L.total (ComplexShape.up ℕ)).d n.pred n b) :=
      included_d_supported L m r n.pred n hmr' hn' e
    have hpb : DoubleComplexProjections.DoubleComplex.πTotal L m (r + 1) n hmr ((L.total (ComplexShape.up ℕ)).d n.pred n b) =
        ((-1 : ℤ) ^ m) • (L.X m).d r (r + 1) e :=
      included_vertical_component L m r n.pred n hmr' hn' e
    have hcomp : DoubleComplexProjections.DoubleComplex.πTotal L m (r + 1) n hmr y =
        ((-1 : ℤ) ^ m) • (φ.f m).f (r + 1) c -
          ((-1 : ℤ) ^ m) • (L.X m).d r (r + 1) e := by
      calc
        DoubleComplexProjections.DoubleComplex.πTotal L m (r + 1) n hmr y =
            ((-1 : ℤ) ^ m) • (((-1 : ℤ) ^ m) • DoubleComplexProjections.DoubleComplex.πTotal L m (r + 1) n hmr y) :=
          (DoubleComplexRelativeBoundary.DoubleComplex.sign_zsmul_involutive m _).symm
        _ = ((-1 : ℤ) ^ m) • ((φ.f m).f (r + 1) c - (L.X m).d r (r + 1) e) :=
          congrArg (fun z => ((-1 : ℤ) ^ m) • z) he
        _ = _ := smul_sub _ _ _
    refine ⟨a, b, hx', ?_⟩
    intro p q hpq hp
    rw [map_add, map_sub]
    by_cases hpm : p < m
    · rw [hys p q hpq hpm, hfa p q hpq hpm, hb p q hpq hpm, sub_zero, zero_add]
    · have hp' : p = m := by omega
      subst p
      have hq : q = r + 1 := by omega
      subst q
      rw [hpa, hpb, hcomp]
      abel

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapReduction.DoubleComplex
