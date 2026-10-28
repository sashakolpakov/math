import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Lattice
import OAI.RepresentationTheory.Theta.Geometric.Torus.Hom

/-! # Fiber Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Two analytic presentations of the same reference fiber have a
canonical complex-linear comparison. It preserves the original lattice,
the Hermitian form, the CM action, and the fixed division-point labels. -/

open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F G : Fiber.ReferenceAnalyticFiber P z)

def Fiber.ReferenceAnalyticFiber.tangentEquiv : Fiber.ReferenceTangent s ≃ₗ[ℂ] Fiber.ReferenceTangent s :=
  (F.projection.quotKerEquivOfSurjective F.surjective).symm.trans
    ((Submodule.quotEquivOfEq _ _ (F.kernel.trans G.kernel.symm)).trans
      (G.projection.quotKerEquivOfSurjective G.surjective))

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_projection (v : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    F.tangentEquiv G (F.projection v) = G.projection v := by
  simp only [Fiber.ReferenceAnalyticFiber.tangentEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_embedding (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    F.tangentEquiv G (F.periodEmbedding v) = G.periodEmbedding v :=
  F.tangentEquiv_projection G _

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_lattice (v : Fiber.ReferenceTangent s) (hv : v ∈ F.lattice) :
    F.tangentEquiv G v ∈ G.lattice := by
  obtain ⟨u, hu, rfl⟩ := (F.lattice_membership v).mp hv
  rw [F.tangentEquiv_projection G]
  exact (G.lattice_membership _).mpr ⟨u, hu, rfl⟩

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_reverse (v : Fiber.ReferenceTangent s) :
    G.tangentEquiv F (F.tangentEquiv G v) = v := by
  obtain ⟨u, rfl⟩ := F.surjective v
  rw [F.tangentEquiv_projection G, G.tangentEquiv_projection F]

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_action (a : NumberField.RingOfIntegers E) (v : Fiber.ReferenceTangent s) :
    F.tangentEquiv G (F.action a v) = G.action a (F.tangentEquiv G v) := by
  have hs : Submodule.span ℝ (F.lattice : Set (Fiber.ReferenceTangent s)) = ⊤ := by
    let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact RepresentationTheory.Theta.Geometric.CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  have he : ((F.tangentEquiv G).toLinearMap.comp (F.action a)).restrictScalars ℝ =
      ((G.action a).comp (F.tangentEquiv G).toLinearMap).restrictScalars ℝ := by
    apply LinearMap.ext_on hs
    intro u hu
    obtain ⟨w, _, rfl⟩ := (F.lattice_membership u).mp hu
    change F.tangentEquiv G (F.action a (F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w))) =
      G.action a (F.tangentEquiv G (F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w)))
    rw [F.equivariant, F.tangentEquiv_projection G, F.tangentEquiv_projection G, G.equivariant]
  exact DFunLike.congr_fun he v

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_form_im (u v : Fiber.ReferenceTangent s) :
    (G.form (F.tangentEquiv G u) (F.tangentEquiv G v)).im = (F.form u v).im := by
  let B := G.imaginaryForm.comp ((F.tangentEquiv G).toLinearMap.restrictScalars ℝ)
  let C := B.compl₂ ((F.tangentEquiv G).toLinearMap.restrictScalars ℝ)
  have hs : Submodule.span ℝ (F.lattice : Set (Fiber.ReferenceTangent s)) = ⊤ := by
    let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact RepresentationTheory.Theta.Geometric.CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  have he : C = F.imaginaryForm := by
    apply LinearMap.ext_on hs
    intro a ha
    apply LinearMap.ext_on hs
    intro b hb
    obtain ⟨a', _, rfl⟩ := (F.lattice_membership a).mp ha
    obtain ⟨b', _, rfl⟩ := (F.lattice_membership b).mp hb
    change (G.form (F.tangentEquiv G (F.projection _)) (F.tangentEquiv G (F.projection _))).im = _
    rw [F.tangentEquiv_projection G, F.tangentEquiv_projection G, G.polarization]
    exact (F.polarization a' b').symm
  exact DFunLike.congr_fun (DFunLike.congr_fun he u) v

theorem Fiber.ReferenceAnalyticFiber.tangentEquiv_form (u v : Fiber.ReferenceTangent s) :
    G.form (F.tangentEquiv G u) (F.tangentEquiv G v) = F.form u v := by
  apply Complex.ext
  · have h := F.tangentEquiv_form_im G u (Complex.I • v)
    rw [map_smul, map_smul, map_smul] at h
    simpa only [smul_eq_mul, Complex.I_mul_im] using h
  · exact F.tangentEquiv_form_im G u v

def Fiber.ReferenceAnalyticFiber.torusMap : F.periodData.periodTorus →+ G.periodData.periodTorus :=
  RepresentationTheory.Theta.Geometric.Torus.Hom.torusLinearMap F.periodData G.periodData (F.tangentEquiv G).toLinearMap
    (F.tangentEquiv_lattice G)

theorem Fiber.ReferenceAnalyticFiber.torusMap_mk (v : Fiber.ReferenceTangent s) :
    F.torusMap G (QuotientAddGroup.mk v) = QuotientAddGroup.mk (F.tangentEquiv G v) := rfl

theorem Fiber.ReferenceAnalyticFiber.torusMap_reverse (t : F.periodData.periodTorus) : G.torusMap F (F.torusMap G t) = t := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact congrArg (QuotientAddGroup.mk : Fiber.ReferenceTangent s → Fiber.ReferenceTangent s ⧸ F.lattice)
    (F.tangentEquiv_reverse G v)

theorem Fiber.ReferenceAnalyticFiber.torusMap_action (hP : P.IsAdmissible) (a : NumberField.RingOfIntegers E)
    (t : F.periodData.periodTorus) :
    F.torusMap G (F.quotientAction hP a t) = G.quotientAction hP a (F.torusMap G t) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact congrArg (QuotientAddGroup.mk : Fiber.ReferenceTangent s → Fiber.ReferenceTangent s ⧸ G.lattice)
    (F.tangentEquiv_action G a v)

theorem Fiber.ReferenceAnalyticFiber.torusMap_division (N : ℕ) (v : P.lattice) :
    F.torusMap G (F.divisionPoint N v) = G.divisionPoint N v := by
  change QuotientAddGroup.mk (F.tangentEquiv G ((N : ℝ)⁻¹ • F.periodEmbedding v.val)) = _
  rw [show F.tangentEquiv G ((N : ℝ)⁻¹ • F.periodEmbedding v.val) =
    (N : ℝ)⁻¹ • F.tangentEquiv G (F.periodEmbedding v.val) from
      map_smul ((F.tangentEquiv G).restrictScalars ℝ) _ _, F.tangentEquiv_embedding G]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
