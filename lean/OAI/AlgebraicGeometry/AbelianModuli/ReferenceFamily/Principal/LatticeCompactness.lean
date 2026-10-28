import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeActionCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers

/-! # Lattice Compactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeCompactness

noncomputable section

/-! Principal congruence on an actual full lattice is commensurable with
its stabilizer. The anisotropic arithmetic theorem therefore applies to
the same subgroup in the full archimedean product. -/

open scoped _root_.NumberField

section LatticeAction

variable {G V : Type*} [Group G] [AddCommGroup V]
  (ρ : G →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V)
  (Γ : Subgroup G) (hΓ : ∀ g, g ∈ Γ ↔ ∀ v, ρ g v ∈ L ↔ v ∈ L)

include hΓ in
theorem principalAction_le_stabilizer (N : ℕ) :
    (Groups.principalLatticeSubgroup L N).comap ρ ≤ Γ := by
  intro g hg
  exact (hΓ g).mpr fun v => (hg.1 v).symm

include hΓ in
theorem principalAction_commensurable [AddGroup.FG L] (N : ℕ) (hN : N ≠ 0) :
    ((Groups.principalLatticeSubgroup L N).comap ρ).Commensurable Γ := by
  refine ⟨LatticeActionCompactness.principalAction_finiteRelIndex ρ L Γ hΓ N hN, ⟨?_⟩⟩
  rw [Subgroup.relIndex_eq_one.mpr (principalAction_le_stabilizer ρ L Γ hΓ N)]
  exact one_ne_zero

end LatticeAction

theorem principalAction_linearSubgroup_map
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (S : Subgroup (V ≃ₗ[R] V)) (L : AddSubgroup V) (N : ℕ) :
    (((Groups.principalLatticeSubgroup (R := ℤ) L N).comap
        (NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers.Construction.restrictScalarsAutomorphismHom.comp S.subtype)).map S.subtype) =
      Groups.principalLatticeSubgroup (R := R) L N ⊓ S := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hh, h.property⟩
  · rintro ⟨hg, hs⟩
    exact ⟨⟨g, hs⟩, hg, rfl⟩

theorem latticeAction_map_stabilizer
    {k Gk V : Type} [Field k] [NumberField k] [Group Gk] [AddCommGroup V]
    {n : ℕ} (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (ρ : Gk →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V)
    (Γ₀ : Subgroup Gk) (hΓ₀ : ∀ g, g ∈ Γ₀ ↔ ∀ v, ρ g v ∈ L ↔ v ∈ L)
    (Λ : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice k n) (r : Gk ≃* G.RationalPoints) (e : V ≃+ (Fin n → k))
    (hact : ∀ g v, e (ρ g v) = G.representation (r g) (e v))
    (hmem : ∀ v, e v ∈ Λ.module ↔ v ∈ L) :
    Γ₀.map r.toMonoidHom = G.latticeStabilizer Λ := by
  ext g
  obtain ⟨g, rfl⟩ := r.surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, hΓ₀]
  change (∀ v, ρ g v ∈ L ↔ v ∈ L) ↔
    ∀ w, G.representation (r g) w ∈ Λ.module ↔ w ∈ Λ.module
  constructor
  · intro h w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [← hact, hmem, hmem]
    exact h v
  · intro h v
    have hw := h (e v)
    rw [← hact, hmem, hmem] at hw
    exact hw

theorem arithmeticPresentation_of_latticeAction_coordinates
    {k Gk V : Type} [Field k] [NumberField k] [Group Gk] [AddCommGroup V]
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup k)
    (ρ : Gk →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V)
    (Γ₀ : Subgroup Gk) (hΓ₀ : ∀ g, g ∈ Γ₀ ↔ ∀ v, ρ g v ∈ L ↔ v ∈ L)
    (Λ : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice k G.dimension) (r : Gk ≃* G.matrixGroup.RationalPoints)
    (e : V ≃+ (Fin G.dimension → k))
    (hact : ∀ g v, e (ρ g v) = G.matrixGroup.representation (r g) (e v))
    (hmem : ∀ v, e v ∈ Λ.module ↔ v ∈ L) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation G ((G.matrixGroup.diagonal Set.univ).comp r.toMonoidHom) Γ₀ := by
  refine ⟨Λ, r, Set.univ, ContinuousMulEquiv.refl _, ?_, ?_, ?_⟩
  · intro v hv
    exact (hv (Set.mem_univ v)).elim
  · exact latticeAction_map_stabilizer G.matrixGroup ρ L Γ₀ hΓ₀ Λ r e hact hmem
  · intro g
    rfl

theorem principalAction_arithmetic_compact
    {k Gk GInf V : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [AddCommGroup V]
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf)
    (ρ : Gk →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V) [AddGroup.FG L]
    (Γ₀ : Subgroup Gk) (hΓ₀ : ∀ g, g ∈ Γ₀ ↔ ∀ v, ρ g v ∈ L ↔ v ∈ L)
    (hmodel : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation G δ Γ₀) (han : NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsAnisotropic G)
    (N : ℕ) (hN : N ≠ 0) :
    CompactSpace (GInf ⧸ ((Groups.principalLatticeSubgroup L N).comap ρ).map δ) :=
  NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness.Construction.arithmetic_compact_of_anisotropic G δ Γ₀ _ hmodel
    (principalAction_commensurable ρ L Γ₀ hΓ₀ N hN) han

theorem principalAction_arithmetic_discrete
    {k Gk GInf V : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [IsTopologicalGroup GInf] [T2Space GInf]
    [AddCommGroup V]
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf)
    (ρ : Gk →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V) [AddGroup.FG L]
    (Γ₀ : Subgroup Gk) (hΓ₀ : ∀ g, g ∈ Γ₀ ↔ ∀ v, ρ g v ∈ L ↔ v ∈ L)
    (hmodel : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation G δ Γ₀) (N : ℕ) (hN : N ≠ 0) :
    DiscreteTopology (((Groups.principalLatticeSubgroup L N).comap ρ).map δ) :=
  NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.arithmetic_subgroup_discrete G δ Γ₀ _ hmodel
    (principalAction_commensurable ρ L Γ₀ hΓ₀ N hN)

def fullLatticeIntegralAction
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    G.RationalPoints →* ((Fin n → k) ≃ₗ[ℤ] (Fin n → k)) :=
  NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers.Construction.restrictScalarsAutomorphismHom.comp G.representation

@[simp] theorem fullLatticeIntegralAction_apply
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) (v : Fin n → k) :
    fullLatticeIntegralAction G g v = Matrix.SpecialLinearGroup.toLin' g.val v := rfl

def fullLatticePrincipalSubgroup
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (Λ : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice k n) (N : ℕ) :
    Subgroup G.RationalPoints :=
  (Groups.principalLatticeSubgroup Λ.module.toAddSubgroup N).comap (fullLatticeIntegralAction G)

theorem fullLatticePrincipalSubgroup_commensurable
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (Λ : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice k n) (N : ℕ) (hN : N ≠ 0) :
    (fullLatticePrincipalSubgroup G Λ N).Commensurable (G.latticeStabilizer Λ) := by
  let : Module.Finite (𝓞 k) Λ.module := Module.Finite.iff_fg.mpr Λ.finite
  let : Module.Finite ℤ Λ.module := Module.Finite.trans (𝓞 k) Λ.module
  let : AddGroup.FG Λ.module.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp inferInstance
  exact principalAction_commensurable (fullLatticeIntegralAction G) Λ.module.toAddSubgroup
    (G.latticeStabilizer Λ) (fun _ => Iff.rfl) N hN

theorem fullLatticePrincipalSubgroup_compact
    {k : Type} [Field k] [NumberField k]
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup k) (Λ : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice k G.dimension)
    (han : NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsAnisotropic G) (N : ℕ) (hN : N ≠ 0) :
    CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (fullLatticePrincipalSubgroup G.matrixGroup Λ N).map
        (G.matrixGroup.diagonal Set.univ)) :=
  NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness.Construction.arithmetic_compact_of_anisotropic G _ _ _
    (NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.canonical_arithmetic_presentation G Λ)
    (fullLatticePrincipalSubgroup_commensurable G.matrixGroup Λ N hN) han

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeCompactness
