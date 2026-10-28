import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.CoordinateSplit
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Koszul Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy

noncomputable section

/-! Wedge multiplication is the actual scalar nullhomotopy of the
exterior Koszul complex. It constructs its native mapping-cone comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex

universe u
variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
  (s : Module.Dual R V) (e : V)

theorem complex_d (n : ℕ) : (KoszulComplex.complex R V s).d (n + 1) n =
    ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n) := by
  dsimp only [KoszulComplex.complex]
  exact ChainComplex.of_d _ _ n

def family (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel j i) :
    (KoszulComplex.complex R V s).X i ⟶ (KoszulComplex.complex R V s).X j := by
  have hj : i + 1 = j := hij
  subst j
  exact ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e i)

theorem family_succ (n : ℕ) : family R V s e n (n + 1) rfl =
    ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n) := rfl

theorem boundary_eq : Homotopy.nullHomotopicMap' (family R V s e) =
    s e • 𝟙 (KoszulComplex.complex R V s) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (k₁ := 1) (k₀ := 0) rfl
        (by intro l hl; change l + 1 = 0 at hl; omega)]
      erw [family_succ, complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_wedge_zero R V s e x
  | succ n =>
      rw [Homotopy.nullHomotopicMap'_f (k₂ := n + 2) (k₁ := n + 1) (k₀ := n) rfl rfl]
      erw [family_succ, family_succ, complex_d, complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (add_comm _ _).trans (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_wedge R V s e n x)

def homotopy : Homotopy (s e • 𝟙 (KoszulComplex.complex R V s)) 0 :=
  (Homotopy.ofEq (boundary_eq R V s e).symm).trans
    (Homotopy.nullHomotopy' (family R V s e))

theorem homotopy_hom (n : ℕ) :
    (homotopy R V s e).hom n (n + 1) = ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n) := by
  simp [homotopy, Homotopy.trans, Homotopy.ofEq, Homotopy.nullHomotopy',
    Homotopy.nullHomotopy, family]
  rfl

variable (W : Type u) [AddCommGroup W] [Module R W] (t : Module.Dual R W)
  (f : W →ₗ[R] V) (hf : s.comp f = t)

abbrev inclusion := KoszulComplex.map R W V t s f hf

def inclusionHomotopy :
    Homotopy ((s e • 𝟙 (KoszulComplex.complex R W t)) ≫ inclusion R V s W t f hf) 0 :=
  (Homotopy.ofEq (by simp only [Linear.smul_comp, Category.id_comp,
    Linear.comp_smul, Category.comp_id])).trans
      (((homotopy R V s e).compLeft (inclusion R V s W t f hf)).trans
        (Homotopy.ofEq comp_zero))

theorem inclusionHomotopy_hom (n : ℕ) :
    (inclusionHomotopy R V s e W t f hf).hom n (n + 1) =
      ModuleCat.ofHom ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n).comp (exteriorPower.map n f)) := by
  simp only [inclusionHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero, homotopy_hom]
  rfl

def coneMap : homotopyCofiber (s e • 𝟙 (KoszulComplex.complex R W t)) ⟶ KoszulComplex.complex R V s :=
  homotopyCofiber.desc _ (inclusion R V s W t f hf)
    (inclusionHomotopy R V s e W t f hf)

theorem inl_coneMap (n : ℕ) :
    homotopyCofiber.inlX (s e • 𝟙 (KoszulComplex.complex R W t)) n (n + 1) rfl ≫
      (coneMap R V s e W t f hf).f (n + 1) =
        ModuleCat.ofHom ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n).comp (exteriorPower.map n f)) := by
  rw [coneMap, homotopyCofiber.inlX_desc_f, inclusionHomotopy_hom]

theorem inr_coneMap (n : ℕ) :
    homotopyCofiber.inrX (s e • 𝟙 (KoszulComplex.complex R W t)) n ≫
      (coneMap R V s e W t f hf).f n = ModuleCat.ofHom (exteriorPower.map n f) := by
  rw [coneMap, homotopyCofiber.inrX_desc_f]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy
