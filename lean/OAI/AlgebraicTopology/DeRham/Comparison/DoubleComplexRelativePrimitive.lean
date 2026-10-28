import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso

/-! # Double Complex Relative Primitive -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive.DoubleComplex

noncomputable section

/-!
# Relative primitives for actual quasi-isomorphisms of module complexes

The inverse direction of the cycle-lifting criterion follows from the genuine
isomorphism on homology. A compatible pair consisting of a source cocycle and
a target primitive therefore admits a relative primitive. The natural-degree
endpoint is included with its zero incoming differential.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]

namespace RelativePrimitiveAux

variable {S T : ShortComplex (ModuleCat.{v} R)}

/-- The canonical class of a concrete kernel element in the native homology object. -/
private def cycleClass (S : ShortComplex (ModuleCat.{v} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
    (LinearMap.range S.moduleCatToCycles).mkQ

private theorem cycleClass_surjective (S : ShortComplex (ModuleCat.{v} R)) :
    Function.Surjective (cycleClass S) :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (LinearMap.range S.moduleCatToCycles).mkQ_surjective

set_option backward.isDefEq.respectTransparency false in
private theorem cycleClass_eq_iff_exists (S : ShortComplex (ModuleCat.{v} R))
    (x y : LinearMap.ker S.g.hom) :
    cycleClass S x = cycleClass S y ↔
      ∃ z : S.X₁, S.f z = (x : S.X₂) - (y : S.X₂) := by
  change S.moduleCatHomologyIso.toLinearEquiv.symm
      ((LinearMap.range S.moduleCatToCycles).mkQ x) =
    S.moduleCatHomologyIso.toLinearEquiv.symm
      ((LinearMap.range S.moduleCatToCycles).mkQ y) ↔ _
  rw [S.moduleCatHomologyIso.toLinearEquiv.symm.injective.eq_iff]
  change (Submodule.Quotient.mk x :
      LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) =
    Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq]
  change (∃ z, S.moduleCatToCycles z = x - y) ↔ _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

private theorem cycleClass_eq_zero_iff_exists (S : ShortComplex (ModuleCat.{v} R))
    (x : LinearMap.ker S.g.hom) :
    cycleClass S x = 0 ↔ ∃ z : S.X₁, S.f z = (x : S.X₂) := by
  simpa using cycleClass_eq_iff_exists S x 0

private def cycleMap (φ : S ⟶ T) :
    LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ fun x => by
    change T.g (φ.τ₂ (x : S.X₂)) = 0
    have h := ConcreteCategory.congr_hom φ.comm₂₃ (x : S.X₂)
    change T.g (φ.τ₂ (x : S.X₂)) = φ.τ₃ (S.g (x : S.X₂)) at h
    exact h.trans (by rw [show S.g (x : S.X₂) = 0 from x.property, map_zero])

private theorem cycleClass_eq_homologyπ (S : ShortComplex (ModuleCat.{v} R))
    (x : LinearMap.ker S.g.hom) :
    cycleClass S x = S.homologyπ (S.moduleCatCyclesIso.inv x) := by
  exact (ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π x).symm

private theorem cycleMap_eq_cyclesMap (φ : S ⟶ T)
    (x : LinearMap.ker S.g.hom) :
    T.moduleCatCyclesIso.inv (cycleMap φ x) =
      (ShortComplex.cyclesMap φ) (S.moduleCatCyclesIso.inv x) := by
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  have hT := ConcreteCategory.congr_hom T.moduleCatCyclesIso_inv_iCycles (cycleMap φ x)
  have hS := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles x
  have hφ := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ)
    (S.moduleCatCyclesIso.inv x)
  change T.iCycles (T.moduleCatCyclesIso.inv (cycleMap φ x)) = φ.τ₂ (x : S.X₂) at hT
  change S.iCycles (S.moduleCatCyclesIso.inv x) = (x : S.X₂) at hS
  change T.iCycles ((ShortComplex.cyclesMap φ) (S.moduleCatCyclesIso.inv x)) =
    φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv x)) at hφ
  exact hT.trans (by rw [hS] at hφ; exact hφ.symm)

private theorem cycleClass_naturality (φ : S ⟶ T)
    (x : LinearMap.ker S.g.hom) :
    (ShortComplex.homologyMap φ) (cycleClass S x) = cycleClass T (cycleMap φ x) := by
  rw [cycleClass_eq_homologyπ, cycleClass_eq_homologyπ, cycleMap_eq_cyclesMap]
  exact ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ)
    (S.moduleCatCyclesIso.inv x)

/-- A genuine homology isomorphism supplies a lift of each target cycle modulo
an actual boundary. -/
theorem shortComplex_cycle_lift_of_quasiIso (φ : S ⟶ T)
    (hφ : ShortComplex.QuasiIso φ) (y : T.X₂) (hy : T.g y = 0) :
    ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x - y := by
  let : ShortComplex.QuasiIso φ := hφ
  have hsurj := (ModuleCat.epi_iff_surjective (ShortComplex.homologyMap φ)).mp inferInstance
  obtain ⟨a, ha⟩ := hsurj (cycleClass T ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := cycleClass_surjective S a
  refine ⟨x, x.property, ?_⟩
  exact (cycleClass_eq_iff_exists T (cycleMap φ x) ⟨y, hy⟩).mp
    ((cycleClass_naturality φ x).symm.trans ha)

/-- Injectivity of the actual homology isomorphism reflects boundaries. -/
theorem shortComplex_boundary_reflection_of_quasiIso (φ : S ⟶ T)
    (hφ : ShortComplex.QuasiIso φ) (x : S.X₂) (hx : S.g x = 0)
    (hb : ∃ z : T.X₁, T.f z = φ.τ₂ x) :
    ∃ z : S.X₁, S.f z = x := by
  let : ShortComplex.QuasiIso φ := hφ
  let x' : LinearMap.ker S.g.hom := ⟨x, hx⟩
  have hz : cycleClass T (cycleMap φ x') = 0 :=
    (cycleClass_eq_zero_iff_exists T (cycleMap φ x')).mpr hb
  have hmap : (ShortComplex.homologyMap φ) (cycleClass S x') = 0 :=
    (cycleClass_naturality φ x').trans hz
  have hinj := (ModuleCat.mono_iff_injective (ShortComplex.homologyMap φ)).mp inferInstance
  have hs : cycleClass S x' = 0 := hinj (hmap.trans (map_zero _).symm)
  exact (cycleClass_eq_zero_iff_exists S x').mp hs

end RelativePrimitiveAux

variable {C D : CochainComplex (ModuleCat.{v} R) ℕ}

/-- A quasi-isomorphism of nonnegative cochain complexes lifts every target
cycle modulo a boundary, with the true zero-endpoint predecessor. -/
theorem cycle_lift_of_quasiIso (f : C ⟶ D) (hf : QuasiIso f)
    (n : ℕ) (y : D.X n) (hy : D.d n (n + 1) y = 0) :
    ∃ x : C.X n, C.d n (n + 1) x = 0 ∧
      ∃ z : D.X n.pred, D.d n.pred n z = f.f n x - y := by
  have hp : (ComplexShape.up ℕ).prev n = n.pred := by cases n <;> simp
  have hφ := (quasiIsoAt_iff' f n.pred n (n + 1) hp (CochainComplex.next ℕ n)).mp
    ((quasiIso_iff f).mp hf n)
  exact RelativePrimitiveAux.shortComplex_cycle_lift_of_quasiIso
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (ComplexShape.up ℕ)
      n.pred n (n + 1)).map f) hφ y hy

/-- A quasi-isomorphism reflects actual boundaries of source cocycles. -/
theorem boundary_reflection_of_quasiIso (f : C ⟶ D) (hf : QuasiIso f)
    (n : ℕ) (x : C.X n) (hx : C.d n (n + 1) x = 0)
    (hb : ∃ z : D.X n.pred, D.d n.pred n z = f.f n x) :
    ∃ z : C.X n.pred, C.d n.pred n z = x := by
  have hp : (ComplexShape.up ℕ).prev n = n.pred := by cases n <;> simp
  have hφ := (quasiIsoAt_iff' f n.pred n (n + 1) hp (CochainComplex.next ℕ n)).mp
    ((quasiIso_iff f).mp hf n)
  exact RelativePrimitiveAux.shortComplex_boundary_reflection_of_quasiIso
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (ComplexShape.up ℕ)
      n.pred n (n + 1)).map f) hφ x hx hb

/-- A compatible source cocycle and target primitive admit a relative primitive.
The formula includes `n=0`, where the target's incoming differential is zero. -/
theorem relative_primitive_succ (f : C ⟶ D) (hf : QuasiIso f)
    (n : ℕ) (a : C.X (n + 1)) (b : D.X n)
    (ha : C.d (n + 1) (n + 2) a = 0)
    (hab : f.f (n + 1) a = D.d n (n + 1) b) :
    ∃ c : C.X n, C.d n (n + 1) c = a ∧
      ∃ e : D.X n.pred, b = f.f n c - D.d n.pred n e := by
  have hprimitive := boundary_reflection_of_quasiIso f hf (n + 1) a ha ⟨b, hab.symm⟩
  change ∃ c : C.X n, C.d n (n + 1) c = a at hprimitive
  obtain ⟨c₀, hc₀⟩ := hprimitive
  have hcomm := ConcreteCategory.congr_hom (f.comm n (n + 1)) c₀
  change D.d n (n + 1) (f.f n c₀) = f.f (n + 1) (C.d n (n + 1) c₀) at hcomm
  have hr : D.d n (n + 1) (b - f.f n c₀) = 0 := by
    rw [map_sub, hcomm, hc₀, ← hab, sub_self]
  obtain ⟨z, hz, e, he⟩ := cycle_lift_of_quasiIso f hf n (b - f.f n c₀) hr
  refine ⟨c₀ + z, ?_, e, ?_⟩
  · rw [map_add, hc₀, hz, add_zero]
  · rw [map_add, he]
    abel

/-- In the lowest relative degree, there is no boundary correction in degree zero. -/
theorem relative_primitive_zero (f : C ⟶ D) (hf : QuasiIso f)
    (a : C.X 1) (b : D.X 0) (ha : C.d 1 2 a = 0)
    (hab : f.f 1 a = D.d 0 1 b) :
    ∃ c : C.X 0, C.d 0 1 c = a ∧ b = f.f 0 c := by
  obtain ⟨c, hc, e, he⟩ := relative_primitive_succ f hf 0 a b ha hab
  refine ⟨c, hc, ?_⟩
  have hshape : D.d 0 0 = 0 := D.shape 0 0 (by decide)
  change b = f.f 0 c - D.d 0 0 e at he
  rw [hshape] at he
  change b = f.f 0 c - 0 at he
  simpa only [sub_zero] using he

/-- A source zero-cocycle killed by a quasi-isomorphism is zero, since there
is no nonzero incoming boundary in degree zero. -/
theorem relative_cycle_zero (f : C ⟶ D) (hf : QuasiIso f)
    (a : C.X 0) (ha : C.d 0 1 a = 0) (hfa : f.f 0 a = 0) : a = 0 := by
  obtain ⟨c, hc⟩ := boundary_reflection_of_quasiIso f hf 0 a ha
    ⟨0, by rw [map_zero, hfa]⟩
  have hshape : C.d 0 0 = 0 := C.shape 0 0 (by decide)
  change C.d 0 0 c = a at hc
  rw [hshape] at hc
  exact hc.symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive.DoubleComplex
