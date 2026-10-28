import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeEq
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus

/-! # Projective Cone -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone

noncomputable section

/-!
# Projective cones for HolomorphicAlgebraicity

These lemmas relate the analytic cone construction to the project's existing
homogeneous projective zero loci. Analytic extension at the vertex remains a
separate step; it is not asserted by the definitions below.
-/

open Filter Set
open scoped _root_.Topology

variable {ι : Type*}

/-- The affine cone on a projective subset, including its vertex. -/
def projectiveCone (Z : Set (Projectivization ℂ (ι → ℂ))) : Set (ι → ℂ) :=
  {v | ∀ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ Z}

theorem zero_mem_projectiveCone (Z : Set (Projectivization ℂ (ι → ℂ))) :
    (0 : ι → ℂ) ∈ projectiveCone Z := by
  intro h
  exact False.elim (h rfl)

theorem mem_projectiveCone_iff (Z : Set (Projectivization ℂ (ι → ℂ)))
    (v : ι → ℂ) (hv : v ≠ 0) :
    v ∈ projectiveCone Z ↔ Projectivization.mk ℂ v hv ∈ Z :=
  ⟨fun h => h hv, fun h _ => h⟩

theorem smul_mem_projectiveCone (Z : Set (Projectivization ℂ (ι → ℂ)))
    (c : ℂ) {v : ι → ℂ} (hv : v ∈ projectiveCone Z) :
    c • v ∈ projectiveCone Z := by
  intro hcv
  have hv0 : v ≠ 0 := by
    intro h
    exact hcv (by simp [h])
  rw [(Projectivization.mk_eq_mk_iff' ℂ (c • v) v hcv hv0).mpr ⟨c, rfl⟩]
  exact hv hv0

/-- A closed projective set has a closed affine cone in the ordinary
complex-coordinate topology, including at the vertex. -/
theorem isClosed_projectiveCone [Fintype ι] (Z : Set (Projectivization ℂ (ι → ℂ)))
    (hZ : IsClosed Z) : IsClosed (projectiveCone Z) := by
  have heq : (projectiveCone Z)ᶜ =
      Subtype.val '' ((Projectivization.mk' ℂ) ⁻¹' Zᶜ) := by
    ext v
    constructor
    · intro hv
      have hv0 : v ≠ 0 := by
        intro h
        exact hv (h ▸ zero_mem_projectiveCone Z)
      refine ⟨⟨v, hv0⟩, ?_, rfl⟩
      exact fun h => hv ((mem_projectiveCone_iff Z v hv0).mpr h)
    · rintro ⟨v, hv, rfl⟩ h
      exact hv (h v.property)
  apply isOpen_compl_iff.mp
  rw [heq]
  have hopen : IsOpen {v : ι → ℂ | v ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  exact hopen.isOpenMap_subtype_val _
    (hZ.isOpen_compl.preimage (ComplexPoints.Analytic.ProjectiveCompactness.continuous_projectivization_mk' ℂ (ι → ℂ)))

variable {d : ℕ}

/-- Once the cone is analytic at its vertex, its finitely many homogeneous
equations descend to the project's actual projective common zero locus. -/
theorem projective_equations_of_analytic_vertex
    (Z : Set (Projectivization ℂ (Fin d → ℂ))) {m : ℕ}
    (f : Fin m → (Fin d → ℂ) → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hZ : ∀ᶠ v in 𝓝 0, v ∈ projectiveCone Z ↔ ∀ i, f i v = 0) :
    ∃ (Q : Finset (MvPolynomial (Fin d) ℂ)) (degree : Q → ℕ)
      (hQ : ∀ q : Q, q.val.IsHomogeneous (degree q)),
      Z = Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus (fun q : Q => q.val) degree hQ := by
  obtain ⟨Q, hQ, hcone⟩ := ConeEq.Constructions.Cone.finite_equations_from_analytic_vertex
    (smul_mem_projectiveCone Z) f hf hZ
  choose degree hdegree using fun q : Q => hQ q.val q.property
  refine ⟨Q, degree, hdegree, ?_⟩
  ext p
  have heq : p.rep ∈ projectiveCone Z ↔
      ∀ q ∈ Q, MvPolynomial.eval p.rep q = 0 := by
    rw [hcone]
    rfl
  rw [mem_projectiveCone_iff Z p.rep p.rep_nonzero, p.mk_rep] at heq
  rw [← p.mk_rep, Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk]
  simpa only [p.mk_rep, Subtype.forall] using heq

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone
