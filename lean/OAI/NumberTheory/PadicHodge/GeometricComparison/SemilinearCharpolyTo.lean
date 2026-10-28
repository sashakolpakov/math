import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Semilinear Charpoly To -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo.SemilinearCharpoly

noncomputable section

/-! Characteristic polynomials under an actual change of coefficient field. -/

universe u v w z
variable {R : Type u} [Field R] {S : Type v} [Field S] (σ : R ≃+* S)

instance invPair : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

instance invPairSymm : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

variable {V : Type w} [AddCommGroup V] [Module R V]
  {W : Type z} [AddCommGroup W] [Module S W]

theorem finite (e : V ≃ₛₗ[σ.toRingHom] W) [FiniteDimensional R V] : FiniteDimensional S W :=
  Module.Finite.of_surjective e.toLinearMap e.surjective

def basis {ι : Type*} (b : Module.Basis ι R V) (e : V ≃ₛₗ[σ.toRingHom] W) :
    Module.Basis ι S W := by
  letI : Module R W := Module.compHom W σ.toRingHom
  let eR : V ≃ₗ[R] W :=
    { e.toAddEquiv with
      map_smul' := fun r x => e.map_smulₛₗ r x }
  exact (b.map eR).mapCoeffs σ (fun _ _ => rfl)

theorem basis_apply {ι : Type*} (b : Module.Basis ι R V) (e : V ≃ₛₗ[σ.toRingHom] W) (i : ι) :
    basis σ b e i = e (b i) := by
  let : Module R W := Module.compHom W σ.toRingHom
  let eR : V ≃ₗ[R] W :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_smulₛₗ r x }
  exact ((b.map eR).mapCoeffs_apply σ (fun _ _ => rfl) i).trans (b.map_apply eR i)

theorem basis_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι R V)
    (e : V ≃ₛₗ[σ.toRingHom] W) (x : V) (i : ι) :
    (basis σ b e).repr (e x) i = σ (b.repr x i) := by
  classical
  have hx : e x = ∑ j, σ (b.repr x j) • basis σ b e j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [basis_apply]
    exact e.map_smulₛₗ _ _
  rw [hx]
  simp [Finsupp.single_apply]

theorem toMatrix_map {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)
    (e : V ≃ₛₗ[σ.toRingHom] W) (T : Module.End R V) (U : Module.End S W)
    (h : ∀ x, e (T x) = U (e x)) :
    LinearMap.toMatrix (basis σ b e) (basis σ b e) U = (LinearMap.toMatrix b b T).map σ := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
  rw [basis_apply, ← h, basis_repr]

theorem charpoly_map [FiniteDimensional R V] [FiniteDimensional S W]
    (e : V ≃ₛₗ[σ.toRingHom] W) (T : Module.End R V) (U : Module.End S W)
    (h : ∀ x, e (T x) = U (e x)) : U.charpoly = T.charpoly.map σ.toRingHom := by
  classical
  let b := Module.finBasis R V
  rw [← LinearMap.charpoly_toMatrix U (basis σ b e), ← LinearMap.charpoly_toMatrix T b,
    toMatrix_map σ b e T U h]
  exact Matrix.charpoly_map _ σ.toRingHom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo.SemilinearCharpoly
