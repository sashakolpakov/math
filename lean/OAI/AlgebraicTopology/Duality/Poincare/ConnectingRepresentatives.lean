import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact

/-! # Connecting Representatives -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives

noncomputable section

/-!
# Actual representatives of the native connecting homomorphism

These formulas identify mathlib's connecting homomorphism by genuine lifts
in a short exact sequence of complexes. They are used to compare cap
products with the pair and support Mayer--Vietoris connecting maps.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R] {c : ComplexShape ℕ}

/-- The categorical lift of a scalar multiple map sends one to the actual
cycle represented by its coefficient. -/
theorem liftCycles_spanSingleton_apply_one
    (C : HomologicalComplex (ModuleCat.{0} R) c) (i j : ℕ) (hj : c.next i = j)
    (x : LinearMap.ker ((C.sc i).g.hom))
    (hx : ModuleCat.ofHom (LinearMap.toSpanSingleton R (C.X i) x.val) ≫ C.d i j = 0) :
    C.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (C.X i) x.val))
      j hj hx (1 : R) = (C.sc i).moduleCatCyclesIso.inv x := by
  apply (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
  have hleft := ConcreteCategory.congr_hom
    (C.liftCycles_i (ModuleCat.ofHom (LinearMap.toSpanSingleton R (C.X i) x.val))
      j hj hx) (1 : R)
  have hright := ConcreteCategory.congr_hom ((C.sc i).moduleCatCyclesIso_inv_iCycles) x
  have hl : (C.iCycles i)
      (C.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (C.X i) x.val))
        j hj hx (1 : R)) = x.val := by
    simpa only [CategoryTheory.comp_apply, ModuleCat.ofHom, ConcreteCategory.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul] using hleft
  have hr : (C.iCycles i) ((C.sc i).moduleCatCyclesIso.inv x) = x.val := hright
  exact hl.trans hr.symm

/-- Mathlib's connecting homomorphism sends a represented cycle to the
represented differential of any lift, with the native sign convention. -/
theorem connecting_eq_of_representatives
    (S : ShortComplex (HomologicalComplex (ModuleCat.{0} R) c)) (hS : S.ShortExact)
    (i j : ℕ) (hij : c.Rel i j)
    (x₃ : LinearMap.ker ((S.X₃.sc i).g.hom)) (x₂ : S.X₂.X i)
    (x₁ : LinearMap.ker ((S.X₁.sc j).g.hom))
    (hx₂ : S.g.f i x₂ = x₃.val) (hx₁ : S.f.f j x₁.val = S.X₂.d i j x₂) :
    hS.δ i j hij ((S.X₃.homologyπ i) ((S.X₃.sc i).moduleCatCyclesIso.inv x₃)) =
      (S.X₁.homologyπ j) ((S.X₁.sc j).moduleCatCyclesIso.inv x₁) := by
  let e₃ : ModuleCat.of R R ⟶ S.X₃.X i :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x₃.val)
  let e₂ : ModuleCat.of R R ⟶ S.X₂.X i :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x₂)
  let e₁ : ModuleCat.of R R ⟶ S.X₁.X j :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x₁.val)
  have hx₃ : S.X₃.d i j x₃.val = 0 := by
    have h : S.X₃.d i (c.next i) x₃.val = 0 := x₃.property
    rwa [c.next_eq' hij] at h
  have he₃ : e₃ ≫ S.X₃.d i j = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change S.X₃.d i j (a • x₃.val) = 0
    rw [map_smul, hx₃, smul_zero]
  have he₂ : e₂ ≫ S.g.f i = e₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change S.g.f i (a • x₂) = a • x₃.val
    rw [map_smul, hx₂]
  have he₁ : e₁ ≫ S.f.f j = e₂ ≫ S.X₂.d i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change S.f.f j (a • x₁.val) = S.X₂.d i j (a • x₂)
    rw [map_smul, map_smul, hx₁]
  have hδ := ConcreteCategory.congr_hom
    (hS.δ_eq i j hij e₃ he₃ e₂ he₂ e₁ he₁ (c.next j) rfl) (1 : R)
  have he₁cycle : e₁ ≫ S.X₁.d j (c.next j) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change S.X₁.d j (c.next j) (a • x₁.val) = 0
    rw [map_smul, show S.X₁.d j (c.next j) x₁.val = 0 from x₁.property, smul_zero]
  simp only [CategoryTheory.comp_apply] at hδ
  erw [liftCycles_spanSingleton_apply_one S.X₃ i j (c.next_eq' hij) x₃ he₃,
    liftCycles_spanSingleton_apply_one S.X₁ j (c.next j) rfl x₁ he₁cycle] at hδ
  exact hδ

/-- The native cohomological connecting map in the explicit cocycle-class API. -/
theorem cohomologyConnecting_eq_of_lift
    (S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : Cohomology.Singular.Representatives.cochainCocycles S.X₃ n) (x₂ : S.X₂.X n)
    (x₁ : Cohomology.Singular.Representatives.cochainCocycles S.X₁ (n + 1))
    (hx₂ : S.g.f n x₂ = x₃.val)
    (hx₁ : S.f.f (n + 1) x₁.val = S.X₂.d n (n + 1) x₂) :
    hS.δ n (n + 1) rfl (Cohomology.Singular.Representatives.cochainClass S.X₃ n x₃) = Cohomology.Singular.Representatives.cochainClass S.X₁ (n + 1) x₁ := by
  rw [Cohomology.Singular.Representatives.cochainClass_eq_homologyπ, Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  exact connecting_eq_of_representatives S hS n (n + 1) rfl x₃ x₂ x₁ hx₂ hx₁

/-- The native homological connecting map in the explicit cycle-class API. -/
theorem homologyConnecting_eq_of_lift
    (S : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : Cohomology.Singular.ChainRepresentatives.chainCycles S.X₃ (n + 1)) (x₂ : S.X₂.X (n + 1))
    (x₁ : Cohomology.Singular.ChainRepresentatives.chainCycles S.X₁ n)
    (hx₂ : S.g.f (n + 1) x₂ = x₃.val)
    (hx₁ : S.f.f n x₁.val = S.X₂.d (n + 1) n x₂) :
    hS.δ (n + 1) n rfl (Cohomology.Singular.ChainRepresentatives.chainClass S.X₃ (n + 1) x₃) = Cohomology.Singular.ChainRepresentatives.chainClass S.X₁ n x₁ := by
  rw [Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ, Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ]
  exact connecting_eq_of_representatives S hS (n + 1) n rfl x₃ x₂ x₁ hx₂ hx₁

/-- The required lifts always exist in an actual short exact sequence;
the differential lift is automatically a cycle. -/
theorem connecting_representatives_exist
    (S : ShortComplex (HomologicalComplex (ModuleCat.{0} R) c)) (hS : S.ShortExact)
    (i j : ℕ) (hij : c.Rel i j)
    (x₃ : LinearMap.ker ((S.X₃.sc i).g.hom)) :
    ∃ (x₂ : S.X₂.X i) (x₁ : LinearMap.ker ((S.X₁.sc j).g.hom)),
      S.g.f i x₂ = x₃.val ∧ S.f.f j x₁.val = S.X₂.d i j x₂ := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  have hsurj : Function.Surjective (S.g.f i) := (hdeg i).moduleCat_surjective_g
  obtain ⟨x₂, hx₂⟩ := hsurj x₃.val
  have hx₃ : S.X₃.d i j x₃.val = 0 := by
    have h : S.X₃.d i (c.next i) x₃.val = 0 := x₃.property
    rwa [c.next_eq' hij] at h
  have hclosed : S.g.f j (S.X₂.d i j x₂) = 0 := by
    have h := ConcreteCategory.congr_hom (S.g.comm i j) x₂
    change S.X₃.d i j (S.g.f i x₂) = S.g.f j (S.X₂.d i j x₂) at h
    rw [hx₂, hx₃] at h
    exact h.symm
  have hlift : ∃ x₁ : S.X₁.X j, S.f.f j x₁ = S.X₂.d i j x₂ :=
    (ShortComplex.moduleCat_exact_iff _).mp (hdeg j).exact _ hclosed
  obtain ⟨x₁, hx₁⟩ := hlift
  have hcycle : x₁ ∈ LinearMap.ker ((S.X₁.sc j).g.hom) := by
    change S.X₁.d j (c.next j) x₁ = 0
    have hinj : Function.Injective (S.f.f (c.next j)) :=
      (hdeg (c.next j)).moduleCat_injective_f
    apply hinj
    rw [map_zero]
    have hcomm := ConcreteCategory.congr_hom (S.f.comm j (c.next j)) x₁
    change S.X₂.d j (c.next j) (S.f.f j x₁) =
      S.f.f (c.next j) (S.X₁.d j (c.next j) x₁) at hcomm
    rw [hx₁] at hcomm
    have hd := ConcreteCategory.congr_hom (S.X₂.d_comp_d i j (c.next j)) x₂
    change S.X₂.d j (c.next j) (S.X₂.d i j x₂) = 0 at hd
    exact hcomm.symm.trans hd
  exact ⟨x₂, ⟨x₁, hcycle⟩, hx₂, hx₁⟩

/-- Every cocycle has actual lifts representing its cohomological
connecting class. -/
theorem cohomologyConnecting_representatives_exist
    (S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : Cohomology.Singular.Representatives.cochainCocycles S.X₃ n) :
    ∃ (x₂ : S.X₂.X n) (x₁ : Cohomology.Singular.Representatives.cochainCocycles S.X₁ (n + 1)),
      S.g.f n x₂ = x₃.val ∧ S.f.f (n + 1) x₁.val = S.X₂.d n (n + 1) x₂ ∧
      hS.δ n (n + 1) rfl (Cohomology.Singular.Representatives.cochainClass S.X₃ n x₃) = Cohomology.Singular.Representatives.cochainClass S.X₁ (n + 1) x₁ := by
  obtain ⟨x₂, x₁, hx₂, hx₁⟩ := connecting_representatives_exist S hS n (n + 1) rfl x₃
  exact ⟨x₂, x₁, hx₂, hx₁, cohomologyConnecting_eq_of_lift S hS n x₃ x₂ x₁ hx₂ hx₁⟩

/-- Every positive-degree cycle has actual lifts representing its
homological connecting class. -/
theorem homologyConnecting_representatives_exist
    (S : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : Cohomology.Singular.ChainRepresentatives.chainCycles S.X₃ (n + 1)) :
    ∃ (x₂ : S.X₂.X (n + 1)) (x₁ : Cohomology.Singular.ChainRepresentatives.chainCycles S.X₁ n),
      S.g.f (n + 1) x₂ = x₃.val ∧ S.f.f n x₁.val = S.X₂.d (n + 1) n x₂ ∧
      hS.δ (n + 1) n rfl (Cohomology.Singular.ChainRepresentatives.chainClass S.X₃ (n + 1) x₃) = Cohomology.Singular.ChainRepresentatives.chainClass S.X₁ n x₁ := by
  obtain ⟨x₂, x₁, hx₂, hx₁⟩ := connecting_representatives_exist S hS (n + 1) n rfl x₃
  exact ⟨x₂, x₁, hx₂, hx₁, homologyConnecting_eq_of_lift S hS n x₃ x₂ x₁ hx₂ hx₁⟩

end

end OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives
