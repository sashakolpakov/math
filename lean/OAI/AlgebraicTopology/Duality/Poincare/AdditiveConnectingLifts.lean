import OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Additive Connecting Lifts -/

namespace OAI.AlgebraicTopology.Duality.Poincare.AdditiveConnectingLifts

noncomputable section

/-!
# Native additive connecting lifts and prescribed representatives

The rational dual support sequence is a sequence of additive-group
complexes. These lemmas work with its actual categorical cycle objects and
connecting map, without replacing it by an assumed module comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem up_next (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 :=
  (ComplexShape.up ℕ).next_eq' rfl

/-- Lifting a map already landing in native cycles recovers that map. -/
theorem additive_liftCycles_asHom_cycle
    (C : CochainComplex AddCommGrpCat.{0} ℕ) (n : ℕ) (x : C.cycles n)
    (h : (AddCommGrpCat.asHom x ≫ C.iCycles n) ≫ C.d n (n + 1) = 0) :
    C.liftCycles (AddCommGrpCat.asHom x ≫ C.iCycles n) (n + 1) (up_next n) h =
      AddCommGrpCat.asHom x := by
  apply (cancel_mono (C.iCycles n)).mp
  rw [C.liftCycles_i]

/-- The native connecting map of additive-group complexes is computed by
an actual lift and its differential. -/
theorem additiveConnecting_eq_of_lift
    (S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : S.X₃.cycles n) (x₂ : S.X₂.X n) (x₁ : S.X₁.cycles (n + 1))
    (hx₂ : S.g.f n x₂ = S.X₃.iCycles n x₃)
    (hx₁ : S.f.f (n + 1) (S.X₁.iCycles (n + 1) x₁) = S.X₂.d n (n + 1) x₂) :
    hS.δ n (n + 1) rfl (S.X₃.homologyπ n x₃) = S.X₁.homologyπ (n + 1) x₁ := by
  let e₃ := AddCommGrpCat.asHom x₃ ≫ S.X₃.iCycles n
  let e₂ := AddCommGrpCat.asHom x₂
  let e₁ := AddCommGrpCat.asHom x₁ ≫ S.X₁.iCycles (n + 1)
  have he₃ : e₃ ≫ S.X₃.d n (n + 1) = 0 := by
    dsimp only [e₃]
    rw [Category.assoc, S.X₃.iCycles_d, comp_zero]
  have he₂ : e₂ ≫ S.g.f n = e₃ := by
    apply AddCommGrpCat.int_hom_ext
    simpa [e₂, e₃, AddCommGrpCat.asHom] using hx₂
  have he₁ : e₁ ≫ S.f.f (n + 1) = e₂ ≫ S.X₂.d n (n + 1) := by
    apply AddCommGrpCat.int_hom_ext
    simpa [e₁, e₂, AddCommGrpCat.asHom] using hx₁
  have hδ := hS.δ_eq n (n + 1) rfl e₃ he₃ e₂ he₂ e₁ he₁ (n + 2) (up_next (n + 1))
  erw [additive_liftCycles_asHom_cycle, additive_liftCycles_asHom_cycle] at hδ
  have h := ConcreteCategory.congr_hom hδ (1 : ℤ)
  simpa [AddCommGrpCat.asHom] using h

/-- Actual native connecting representatives exist by degreewise exactness. -/
theorem additiveConnecting_representatives_exist
    (S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : S.X₃.cycles n) :
    ∃ (x₂ : S.X₂.X n) (x₁ : S.X₁.cycles (n + 1)),
      S.g.f n x₂ = S.X₃.iCycles n x₃ ∧
      S.f.f (n + 1) (S.X₁.iCycles (n + 1) x₁) = S.X₂.d n (n + 1) x₂ ∧
      hS.δ n (n + 1) rfl (S.X₃.homologyπ n x₃) = S.X₁.homologyπ (n + 1) x₁ := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  have hsurj : Function.Surjective (S.g.f n) := (hdeg n).ab_surjective_g
  obtain ⟨x₂, hx₂⟩ := hsurj (S.X₃.iCycles n x₃)
  have hclosed : S.g.f (n + 1) (S.X₂.d n (n + 1) x₂) = 0 := by
    have h := ConcreteCategory.congr_hom (S.g.comm n (n + 1)) x₂
    change S.X₃.d n (n + 1) (S.g.f n x₂) = S.g.f (n + 1) (S.X₂.d n (n + 1) x₂) at h
    rw [hx₂] at h
    have hz := ConcreteCategory.congr_hom (S.X₃.iCycles_d n (n + 1)) x₃
    exact h.symm.trans hz
  have hlift : ∃ a : S.X₁.X (n + 1), S.f.f (n + 1) a = S.X₂.d n (n + 1) x₂ :=
    (ShortComplex.ab_exact_iff _).mp (hdeg (n + 1)).exact _ hclosed
  obtain ⟨a, ha⟩ := hlift
  have hcycle : S.X₁.d (n + 1) (n + 2) a = 0 := by
    have hinj : Function.Injective (S.f.f (n + 2)) := (hdeg (n + 2)).ab_injective_f
    apply hinj
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (S.f.comm (n + 1) (n + 2)) a
    change S.X₂.d (n + 1) (n + 2) (S.f.f (n + 1) a) =
      S.f.f (n + 2) (S.X₁.d (n + 1) (n + 2) a) at h
    rw [ha] at h
    exact h.symm.trans (ConcreteCategory.congr_hom (S.X₂.d_comp_d n (n + 1) (n + 2)) x₂)
  have he : AddCommGrpCat.asHom a ≫ S.X₁.d (n + 1) (n + 2) = 0 := by
    apply AddCommGrpCat.int_hom_ext
    simpa [AddCommGrpCat.asHom] using hcycle
  let x₁ := S.X₁.liftCycles (AddCommGrpCat.asHom a) (n + 2) (up_next (n + 1)) he (1 : ℤ)
  have hx₁ : S.X₁.iCycles (n + 1) x₁ = a := by
    have h := ConcreteCategory.congr_hom
      (S.X₁.liftCycles_i (AddCommGrpCat.asHom a) (n + 2) (up_next (n + 1)) he) (1 : ℤ)
    change S.X₁.iCycles (n + 1) x₁ = AddCommGrpCat.asHom a (1 : ℤ) at h
    exact h.trans (by simp [AddCommGrpCat.asHom])
  refine ⟨x₂, x₁, hx₂, ?_, ?_⟩
  · rw [hx₁]
    exact ha
  · exact additiveConnecting_eq_of_lift S hS n x₃ x₂ x₁ hx₂ (by rwa [hx₁])

/-- A null class in positive degree has a native incoming primitive. -/
theorem additiveCochain_primitive_of_homologyπ_zero
    (C : CochainComplex AddCommGrpCat.{0} ℕ) (n : ℕ)
    (x : C.cycles (n + 1)) (hx : C.homologyπ (n + 1) x = 0) :
    ∃ a : C.X n, C.toCycles n (n + 1) a = x := by
  let S := ShortComplex.mk (C.toCycles n (n + 1)) (C.homologyπ (n + 1))
    (C.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel n (n + 1) ((ComplexShape.up ℕ).prev_eq' rfl))
  exact (ShortComplex.ab_exact_iff S).mp hS x hx

/-- Choose the middle lift so that its differential is exactly a prescribed
cycle representing the connecting class. The correction is an actual boundary. -/
theorem additiveConnecting_lift_preferred
    (S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)) (hS : S.ShortExact)
    (n : ℕ) (x₃ : S.X₃.cycles n) (y₁ : S.X₁.cycles (n + 1))
    (hy₁ : hS.δ n (n + 1) rfl (S.X₃.homologyπ n x₃) = S.X₁.homologyπ (n + 1) y₁) :
    ∃ x₂ : S.X₂.X n, S.g.f n x₂ = S.X₃.iCycles n x₃ ∧
      S.f.f (n + 1) (S.X₁.iCycles (n + 1) y₁) = S.X₂.d n (n + 1) x₂ := by
  obtain ⟨x₂, x₁, hx₂, hx₁, hδ⟩ := additiveConnecting_representatives_exist S hS n x₃
  have hzero : S.X₁.homologyπ (n + 1) (x₁ - y₁) = 0 := by
    rw [map_sub, ← hδ, hy₁, sub_self]
  obtain ⟨a, ha⟩ := additiveCochain_primitive_of_homologyπ_zero S.X₁ n (x₁ - y₁) hzero
  have hda : S.X₁.d n (n + 1) a =
      S.X₁.iCycles (n + 1) x₁ - S.X₁.iCycles (n + 1) y₁ := by
    have h := (ConcreteCategory.congr_hom (S.X₁.toCycles_i n (n + 1)) a).symm.trans
      (congrArg (S.X₁.iCycles (n + 1)) ha)
    simpa only [map_sub] using h
  refine ⟨x₂ - S.f.f n a, ?_, ?_⟩
  · rw [map_sub, hx₂]
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom S.zero n) a
    change S.g.f n (S.f.f n a) = 0 at h
    rw [h, sub_zero]
  · rw [map_sub]
    have h := ConcreteCategory.congr_hom (S.f.comm n (n + 1)) a
    change S.X₂.d n (n + 1) (S.f.f n a) = S.f.f (n + 1) (S.X₁.d n (n + 1) a) at h
    rw [h, hda, map_sub, ← hx₁]
    abel

/-- Through an actual quasi-isomorphism into the first term, the preferred
connecting representative can be chosen in the source complex itself. -/
theorem additiveConnecting_representatives_through_quasiIso
    (S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)) (hS : S.ShortExact)
    {T : CochainComplex AddCommGrpCat.{0} ℕ} (F : T ⟶ S.X₁) (n : ℕ)
    [QuasiIsoAt F (n + 1)] (x₃ : S.X₃.cycles n) :
    ∃ (x₂ : S.X₂.X n) (c : T.cycles (n + 1)),
      S.g.f n x₂ = S.X₃.iCycles n x₃ ∧
      S.f.f (n + 1) (F.f (n + 1) (T.iCycles (n + 1) c)) = S.X₂.d n (n + 1) x₂ ∧
      homologyMap F (n + 1) (T.homologyπ (n + 1) c) =
        hS.δ n (n + 1) rfl (S.X₃.homologyπ n x₃) := by
  let e := isoOfQuasiIsoAt F (n + 1)
  let hclass := hS.δ n (n + 1) rfl (S.X₃.homologyπ n x₃)
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (T.homologyπ (n + 1))).mp
    inferInstance (e.inv hclass)
  have hFc : homologyMap F (n + 1) (T.homologyπ (n + 1) c) = hclass := by
    change e.hom (T.homologyπ (n + 1) c) = hclass
    rw [hc]
    exact ConcreteCategory.congr_hom e.inv_hom_id hclass
  have hy : hS.δ n (n + 1) rfl (S.X₃.homologyπ n x₃) =
      S.X₁.homologyπ (n + 1) (cyclesMap F (n + 1) c) := by
    have h := ConcreteCategory.congr_hom (homologyπ_naturality F (n + 1)) c
    exact hFc.symm.trans h
  obtain ⟨x₂, hx₂, hx₁⟩ := additiveConnecting_lift_preferred S hS n x₃
    (cyclesMap F (n + 1) c) hy
  have hi := ConcreteCategory.congr_hom (cyclesMap_i F (n + 1)) c
  change S.X₁.iCycles (n + 1) (cyclesMap F (n + 1) c) =
    F.f (n + 1) (T.iCycles (n + 1) c) at hi
  refine ⟨x₂, c, hx₂, ?_, hFc⟩
  rwa [hi] at hx₁

end

end OAI.AlgebraicTopology.Duality.Poincare.AdditiveConnectingLifts
