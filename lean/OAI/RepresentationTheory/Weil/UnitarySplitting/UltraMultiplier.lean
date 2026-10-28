import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest
import OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg

/-! # Ultra Multiplier -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction

/-! Identification of the Bruhat space and the genuine Weyl action over
ultrametric fields. -/

open _root_.MeasureTheory
open scoped BigOperators _root_.Topology

variable {F : Type} [NormedField F] [IsUltrametricDist F] {d : ℕ}

theorem schwartzBruhat_ultra_iff {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} :
    f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ↔ IsLocallyConstant f ∧ HasCompactSupport f := by
  refine ⟨fun hf => ?_, fun hf => Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem hf.1 hf.2⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨r, e, φ, rfl⟩
      · exact hf
      · let : ConnectedSpace (Local.FunctionsMetaplectic.Construction.Position F d) := e.toHomeomorph.connectedSpace_iff.mp inferInstance
        let : Subsingleton (Local.FunctionsMetaplectic.Construction.Position F d) := subsingleton_of_preconnected_totallyDisconnected
        exact ⟨IsLocallyConstant.of_discrete _, HasCompactSupport.of_compactSpace _⟩
  | zero => exact ⟨IsLocallyConstant.const _, HasCompactSupport.zero⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  | smul c f _ hf => exact ⟨hf.1.comp (fun z => c • z), hf.2.smul_left⟩

theorem heisenbergFunction_ultra_mem (ψ : AddChar F ℂ)
    (hψ : Continuous (fun x : F => ψ x)) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  obtain ⟨hf, hc⟩ := schwartzBruhat_ultra_iff.mp hf
  let q : Local.FunctionsMetaplectic.Construction.Position F d := fun i => v (Sum.inl i)
  have ht : Continuous (fun x : Local.FunctionsMetaplectic.Construction.Position F d => x - q) := continuous_id.sub continuous_const
  have hphase : Continuous (fun x : Local.FunctionsMetaplectic.Construction.Position F d =>
      ∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) := by fun_prop
  apply Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact ((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hψ).comp_continuous hphase).mul
      (hf.comp_continuous ht)
  · exact (hc.comp_homeomorph (Homeomorph.subRight q)).mul_left

variable [CharZero F]

def ultraHeisenbergOperator (ψ : AddChar F ℂ)
    (hψ : Continuous (fun x : F => ψ x)) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun f := ⟨Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val, heisenbergFunction_ultra_mem ψ hψ v f.property⟩
  invFun f := ⟨Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) f.val,
    heisenbergFunction_ultra_mem ψ hψ (-v) f.property⟩
  left_inv f := Subtype.ext (Heisenberg.Construction.heisenbergFunction_neg_left_cancel ψ v f.val)
  right_inv f := Subtype.ext (Heisenberg.Construction.heisenbergFunction_neg_right_cancel ψ v f.val)
  map_add' f g := Subtype.ext ((Heisenberg.Construction.heisenbergLinearEquiv ψ v).map_add f.val g.val)
  map_smul' z f := Subtype.ext (Oscillator.Construction.heisenbergFunction_smul d ψ v z f.val)

end RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction

namespace RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Locality

/-! An algebraic locality argument for compact locally constant functions.
A linear operator commuting with locally constant, point-separating
multipliers cannot create support. -/

open scoped BigOperators

variable {X I : Type} [TopologicalSpace X]
variable (S : Submodule ℂ (X → ℂ)) (χ : I → X → ℂ)
variable (M : I → S →ₗ[ℂ] S)

def productOperator (l : List (I × ℂ)) : S →ₗ[ℂ] S :=
  l.foldr (fun p B => (M p.1 - p.2 • LinearMap.id).comp B) LinearMap.id

omit [TopologicalSpace X] in
theorem productOperator_apply
    (hM : ∀ i (f : S) x, (M i f).val x = χ i x * f.val x)
    (l : List (I × ℂ)) (f : S) (x : X) :
    (productOperator S M l f).val x =
      (l.map (fun p => χ p.1 x - p.2)).prod * f.val x := by
  induction l with
  | nil => simp [productOperator]
  | cons p l ih =>
      change (M p.1 (productOperator S M l f)).val x -
        p.2 * (productOperator S M l f).val x = _
      rw [hM, ih]
      simp only [List.map_cons, List.prod_cons]
      ring

omit [TopologicalSpace X] in
theorem productOperator_commutes (A : S →ₗ[ℂ] S)
    (hA : ∀ i f, A (M i f) = M i (A f))
    (l : List (I × ℂ)) (f : S) :
    A (productOperator S M l f) = productOperator S M l (A f) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      change A (M p.1 (productOperator S M l f) - p.2 • productOperator S M l f) =
        M p.1 (productOperator S M l (A f)) - p.2 • productOperator S M l (A f)
      rw [map_sub, map_smul, hA, ih]

theorem preserves_zero_at
    (hχ : ∀ i, IsLocallyConstant (χ i))
    (hsep : ∀ x y : X, x ≠ y → ∃ i, χ i x ≠ χ i y)
    (hM : ∀ i (f : S) x, (M i f).val x = χ i x * f.val x)
    (A : S →ₗ[ℂ] S) (hA : ∀ i f, A (M i f) = M i (A f))
    (f : S) (hf : IsLocallyConstant f.val) (hc : HasCompactSupport f.val)
    (x : X) (hx : f.val x = 0) : (A f).val x = 0 := by
  classical
  have hclosed : IsClosed (Function.support f.val) := by
    convert (hf.isOpen_fiber 0).isClosed_compl using 1
    ext y
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_ofPred_eq]
  have hsupport : tsupport f.val = Function.support f.val := hclosed.closure_eq
  have hxout : x ∉ tsupport f.val := by simpa [hsupport, Function.mem_support] using hx
  let J := {p : I × ℂ // χ p.1 x ≠ p.2}
  let U : J → Set X := fun p => {y | χ p.val.1 y = p.val.2}
  have hopen (p : J) : IsOpen (U p) := (hχ p.val.1).isOpen_fiber p.val.2
  have hcover : tsupport f.val ⊆ ⋃ p : J, U p := by
    intro y hy
    have hxy : x ≠ y := by rintro rfl; exact hxout hy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact Set.mem_iUnion.mpr ⟨⟨(i, χ i y), hi⟩, rfl⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hopen hcover
  let l : List (I × ℂ) := s.toList.map Subtype.val
  have hzero : productOperator S M l f = 0 := by
    apply Subtype.ext
    funext y
    rw [productOperator_apply S χ M hM]
    by_cases hfy : f.val y = 0
    · simp [hfy]
    · have hy : y ∈ tsupport f.val := by simpa [hsupport, Function.mem_support] using hfy
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (hs hy)
      have hz : (0 : ℂ) ∈ l.map (fun p => χ p.1 y - p.2) := by
        apply List.mem_map.mpr
        refine ⟨p.val, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hp, rfl⟩
        · exact sub_eq_zero.mpr hyp
      rw [List.prod_eq_zero hz, zero_mul]
      rfl
  have hnonzero : (l.map (fun p => χ p.1 x - p.2)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    obtain ⟨p, hp, hpzero⟩ := List.mem_map.mp hz
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hp
    exact (sub_ne_zero.mpr p.property) hpzero
  have hh := congrArg (fun g : S => g.val x) (productOperator_commutes S M A hA l f)
  rw [hzero, map_zero] at hh
  have hprod := productOperator_apply S χ M hM l (A f) x
  change 0 = (productOperator S M l (A f)).val x at hh
  rw [hprod] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left hnonzero

end RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Locality

namespace RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction
section

/-! The commutant of translations and modulations on the nonarchimedean
Bruhat space consists of scalar operators. -/

open scoped BigOperators

variable {F : Type} [NormedField F] [IsUltrametricDist F] [CharZero F] {d : ℕ}

def modulationCharacter (ψ : AddChar F ℂ) (p : Local.FunctionsMetaplectic.Construction.Position F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) : ℂ :=
  ψ (Local.FunctionsMetaplectic.Construction.dot p x)

omit [IsUltrametricDist F] [CharZero F] in
theorem modulationCharacter_separates (ψ : AddChar F ℂ)
    (hψ : ∃ t, ψ t ≠ 1) (hunit : ∀ t, ‖ψ t‖ = 1)
    (x y : Local.FunctionsMetaplectic.Construction.Position F d) (hxy : x ≠ y) :
    ∃ p, modulationCharacter ψ p x ≠ modulationCharacter ψ p y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  obtain ⟨t, ht⟩ := hψ
  let p : Local.FunctionsMetaplectic.Construction.Position F d := Pi.single i (t / (x i - y i))
  refine ⟨p, fun hh => ht ?_⟩
  have hp : Local.FunctionsMetaplectic.Construction.dot p x - Local.FunctionsMetaplectic.Construction.dot p y = t := by
    simp only [Local.FunctionsMetaplectic.Construction.dot, p, Pi.single_apply]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  rw [← hp, ψ.map_sub_eq_div]
  change ψ (Local.FunctionsMetaplectic.Construction.dot p x) = ψ (Local.FunctionsMetaplectic.Construction.dot p y) at hh
  rw [hh, div_self]
  intro hz
  have hn := hunit (Local.FunctionsMetaplectic.Construction.dot p y)
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

omit [CharZero F] in
theorem modulationCharacter_locallyConstant (ψ : AddChar F ℂ)
    (hψ : Continuous (fun x : F => ψ x)) (p : Local.FunctionsMetaplectic.Construction.Position F d) :
    IsLocallyConstant (modulationCharacter ψ p) := by
  apply (LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hψ).comp_continuous
  unfold Local.FunctionsMetaplectic.Construction.dot
  fun_prop

def ultraModulationOperator (ψ : AddChar F ℂ)
    (hψ : Continuous (fun x : F => ψ x)) (p : Local.FunctionsMetaplectic.Construction.Position F d) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  (ultraHeisenbergOperator ψ hψ (Sum.elim 0 p)).toLinearMap

theorem ultraModulationOperator_apply (ψ : AddChar F ℂ)
    (hψ : Continuous (fun x : F => ψ x)) (p : Local.FunctionsMetaplectic.Construction.Position F d)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    (ultraModulationOperator ψ hψ p f).val x = modulationCharacter ψ p x * f.val x := by
  change Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim 0 p) f.val x = _
  simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction, modulationCharacter, Local.FunctionsMetaplectic.Construction.dot]

theorem ultra_commutant_preserves_zero
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
    (hnontrivial : ∃ t, ψ t ≠ 1) (hunit : ∀ t, ‖ψ t‖ = 1)
    (A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ p f, A (ultraModulationOperator ψ hψ p f) =
      ultraModulationOperator ψ hψ p (A f))
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) (hx : f.val x = 0) :
    (A f).val x = 0 := by
  obtain ⟨hf, hc⟩ := schwartzBruhat_ultra_iff.mp f.property
  exact Locality.preserves_zero_at
    (Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (modulationCharacter ψ) (ultraModulationOperator ψ hψ)
    (modulationCharacter_locallyConstant ψ hψ)
    (modulationCharacter_separates ψ hnontrivial hunit)
    (ultraModulationOperator_apply ψ hψ) A hA f hf hc x hx

theorem ultraTranslation_apply (ψ : AddChar F ℂ)
    (hψ : Continuous (fun x : F => ψ x)) (q : Local.FunctionsMetaplectic.Construction.Position F d)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    (ultraHeisenbergOperator ψ hψ (Sum.elim q 0) f).val x = f.val (x - q) := by
  change Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim q 0) f.val x = _
  simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction, Pi.sub_def]

theorem ultra_commutant_scalar [LocallyCompactSpace F]
    (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
    (hnontrivial : ∃ t, ψ t ≠ 1) (hunit : ∀ t, ‖ψ t‖ = 1)
    (A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ v f, A (ultraHeisenbergOperator ψ hψ v f) =
      ultraHeisenbergOperator ψ hψ v (A f)) :
    ∃ z : ℂ, ∀ f, A f = z • f := by
  let u := LocalTest.Construction.ultraTestVector F hF d
  let z := (A u).val 0
  refine ⟨z, fun f => ?_⟩
  apply Subtype.ext
  funext x
  let t := ultraHeisenbergOperator ψ hψ (Sum.elim x 0) u
  have ht : t.val x = 1 := by
    change (ultraHeisenbergOperator ψ hψ (Sum.elim x 0) u).val x = 1
    rw [ultraTranslation_apply, sub_self]
    exact LocalTest.Construction.ultraTestVector_at_zero F hF d
  have hAt : (A t).val x = z := by
    change (A (ultraHeisenbergOperator ψ hψ (Sum.elim x 0) u)).val x = z
    rw [hA, ultraTranslation_apply, sub_self]
  have hzero : (f - f.val x • t).val x = 0 := by
    change f.val x - f.val x * t.val x = 0
    rw [ht, mul_one, sub_self]
  have hh := ultra_commutant_preserves_zero ψ hψ hnontrivial hunit A
    (fun p g => hA (Sum.elim 0 p) g) (f - f.val x • t) x hzero
  rw [map_sub, map_smul] at hh
  change (A f).val x - f.val x * (A t).val x = 0 at hh
  rw [hAt] at hh
  change (A f).val x = z * f.val x
  exact (sub_eq_zero.mp hh).trans (mul_comm _ _)

end

/-! Identification of the circle-extension kernel in the ultrametric case,
using the proved commutant theorem on the actual Bruhat space. -/

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [IsUltrametricDist F] [CharZero F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
variable (σ : E ≃ₐ[F] E)
variable (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ)

theorem kernel_commutes_ultra
    (hψ : Continuous (fun x : F => ψ x))
    (a : Oscillator.Construction.CircleExtension σ H K c ψ) (ha : Oscillator.Construction.circleProjection σ H K c ψ a = 1)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
    a.val.2 (ultraHeisenbergOperator ψ hψ v f) =
      ultraHeisenbergOperator ψ hψ v (a.val.2 f) := by
  have hgraph : Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (c.coordinates (c.coordinates.symm v)) f
      (ultraHeisenbergOperator ψ hψ v f) := by
    rw [c.coordinates.apply_symm_apply]
    rfl
  have hh := (a.property.2 (c.coordinates.symm v) f
    (ultraHeisenbergOperator ψ hψ v f)).mp hgraph
  have ha' : a.val.1 = 1 := ha
  change (a.val.2 (ultraHeisenbergOperator ψ hψ v f)).val =
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates (a.val.1.val (c.coordinates.symm v)))
      (a.val.2 f).val at hh
  rw [ha'] at hh
  change (a.val.2 (ultraHeisenbergOperator ψ hψ v f)).val =
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates (c.coordinates.symm v)) (a.val.2 f).val at hh
  rw [c.coordinates.apply_symm_apply] at hh
  exact Subtype.ext hh

theorem circleProjection_kernel_ultra
    (hF : ¬ DiscreteTopology F)
    (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hnontrivial : ∃ t, ψ t ≠ 1) (a : Oscillator.Construction.CircleExtension σ H K c ψ) :
    Oscillator.Construction.circleProjection σ H K c ψ a = 1 ↔
      ∃ z : Circle, Oscillator.Construction.circleScalar σ H K c ψ z = a := by
  constructor
  · intro ha
    obtain ⟨z, hz⟩ := ultra_commutant_scalar hF ψ hψ hnontrivial hunit a.val.2.toLinearMap
      (kernel_commutes_ultra σ H K c ψ hψ a ha)
    let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
    let u := LocalTest.Construction.ultraTestVector F hF (m * n)
    have hun : ‖Weak.Construction.testToL2 F (m * n) u‖ ≠ 0 := by
      intro hh
      have heq : Weak.Construction.testToL2 F (m * n) u = Weak.Construction.testToL2 F (m * n) 0 := by
        rw [map_zero]
        exact norm_eq_zero.mp hh
      exact LocalTest.Construction.ultraTestVector_ne_zero F hF (m * n) (Weak.Construction.testToL2_injective F (m * n) heq)
    have hnorm : ‖z‖ = 1 := by
      have hh : ‖Weak.Construction.testToL2 F (m * n) (a.val.2 u)‖ = ‖Weak.Construction.testToL2 F (m * n) u‖ := by
        rw [Weak.Construction.testToL2_norm, Weak.Construction.testToL2_norm, a.property.1]
      rw [show a.val.2 u = z • u from hz u, map_smul, norm_smul] at hh
      exact (mul_right_cancel₀ hun (hh.trans (one_mul _).symm))
    let ζ : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hnorm⟩
    refine ⟨ζ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ha.symm
    · apply LinearEquiv.ext
      intro f
      exact (hz f).symm
  · rintro ⟨z, rfl⟩
    exact Oscillator.Construction.circleScalar_projects_to_one σ H K c ψ z

end RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction

end

end OAI
