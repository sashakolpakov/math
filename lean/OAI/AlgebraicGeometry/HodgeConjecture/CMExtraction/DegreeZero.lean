import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Degree
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Retraction

/-! # Degree Zero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DegreeZero.Local

noncomputable section

/-! Every GL3 kernel of determinant degree one comes from the actual
SL3 spherical algebra. In particular this applies to the three concrete
central-normalized minuscule products. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

theorem gl3_degree_one_activeCoset (c : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)
    (hc : HeckeDegree.Local.heckeCosetDegree (C := Degree.Local.GL3Degree q) (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (Degree.Local.gl3DeterminantDegree q)
      (Degree.Local.gl3DeterminantDegree_integral q) c = 1) :
    CosetsKernel.Local.activeGL3CosetMap q v c ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeOrbit q v := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hd : Matrix.GeneralLinearGroup.det g ∈ RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q :=
    (QuotientGroup.eq_one_iff _).mp hc
  refine ⟨CosetsKernel.Local.activeGL3Embedding q v g, ?_, rfl⟩
  rw [RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeSector_eq_allowed]
  change (CosetsKernel.Local.activeGL3Embedding q v g).1 v ∈ RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.unitDetGL q ∧
    (∀ w, w ≠ v → (CosetsKernel.Local.activeGL3Embedding q v g).1 w ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) ∧
      (CosetsKernel.Local.activeGL3Embedding q v g).2 ∈ RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q
  rw [CosetsKernel.Local.activeGL3Embedding_self]
  refine ⟨hd, ?_, (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q).one_mem⟩
  intro w hw
  change (if w = v then g else 1) ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q
  simpa only [ite_eq_right hw] using (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q).one_mem

theorem gl3_degree_one_mem_active {T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)} (hT : Degree.Local.IsGL3Homogeneous q T 1) :
    CosetsKernel.Local.activeGL3HeckeMap q v T ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q v := by
  apply RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.supported_kernel_mem_active q v
  change AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (CosetsKernel.Local.activeGL3HeckeMap q v T) ∈ _
  rw [CosetsKernel.Local.activeGL3HeckeMap_kernel]
  apply (Finsupp.mem_supported' ℚ _).mpr
  intro x hx
  change Finsupp.mapDomain (CosetsKernel.Local.activeGL3CosetMap q v)
    (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) x = 0
  by_cases hr : x ∈ Set.range (CosetsKernel.Local.activeGL3CosetMap q v)
  · obtain ⟨c, rfl⟩ := hr
    rw [Finsupp.mapDomain_apply_of_injective (CosetsKernel.Local.activeGL3CosetMap_injective q v)]
    exact (Finsupp.mem_supported' ℚ _).mp hT c (fun hc => hx (gl3_degree_one_activeCoset q v c hc))
  · exact Finsupp.mapDomain_of_notMem_range _ _ hr

theorem gl3_degree_one_from_sl3 {T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)} (hT : Degree.Local.IsGL3Homogeneous q T 1) :
    ∃ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, Retraction.Local.sl3ToGL3Hecke q v S = T := by
  let A : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q v := ⟨CosetsKernel.Local.activeGL3HeckeMap q v T, gl3_degree_one_mem_active q v hT⟩
  refine ⟨(RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v).symm A, ?_⟩
  apply CosetsKernel.Local.activeGL3HeckeMap_injective q v
  rw [Retraction.Local.sl3ToGL3Hecke_factorization]
  change (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v ((RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v).symm A)).val = _
  rw [AlgEquiv.apply_symm_apply]

theorem gl3_minuscule_invariants_from_sl3 :
    (∃ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, Retraction.Local.sl3ToGL3Hecke q v S =
      Minuscule.Local.gl3MinusculeHecke q 1 ^ 3 * (Degree.Local.gl3CentralUnit q).inv) ∧
    (∃ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, Retraction.Local.sl3ToGL3Hecke q v S =
      Minuscule.Local.gl3MinusculeHecke q 2 ^ 3 * (Degree.Local.gl3CentralUnit q).inv ^ 2) ∧
    (∃ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, Retraction.Local.sl3ToGL3Hecke q v S =
      Minuscule.Local.gl3MinusculeHecke q 1 * Minuscule.Local.gl3MinusculeHecke q 2 * (Degree.Local.gl3CentralUnit q).inv) :=
  ⟨gl3_degree_one_from_sl3 q v (Degree.Local.gl3_first_cube_degree_one q),
    gl3_degree_one_from_sl3 q v (Degree.Local.gl3_second_cube_degree_one q),
    gl3_degree_one_from_sl3 q v (Degree.Local.gl3_mixed_degree_one q)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DegreeZero.Local
