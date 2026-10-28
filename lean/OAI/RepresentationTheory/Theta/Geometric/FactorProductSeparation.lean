import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyProducts

/-! # Factor Product Separation -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Multiplying by a generated family with another automorphy factor
preserves point separation and tangent detection. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J K : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family K) (h : G.degree = F.degree)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_left (p v : Φ.space) (hF : F.Detects p v) :
    (F.factorMul G h).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hF
  obtain ⟨g, hg, hgp⟩ := G.nonzero p
  refine ⟨s.factorMul (g.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h s hs g hg,
    t.factorMul (g.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h t ht g hg, ?_, ?_⟩
  · rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply]
    exact mul_ne_zero hsp hgp
  · apply sub_ne_zero.mp
    change Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.wronskian (s.factorMul (g.castDegree h)) (t.factorMul (g.castDegree h)) p v ≠ 0
    rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_cast_coe, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_cast_coe,
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.wronskian_mul_right _ _ _ _ _ (s.differentiable p) (t.differentiable p) (g.differentiable p)]
    exact mul_ne_zero (pow_ne_zero 2 hgp) (sub_ne_zero.mpr hdet)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_left (p q : Φ.space) (hF : F.Separates p q) :
    (F.factorMul G h).Separates p q := by
  obtain ⟨s, hs, t, ht, hdet⟩ := hF
  obtain ⟨g, hg, hgp⟩ := G.nonzero p
  by_cases hgq : g q = 0
  · obtain ⟨k, hk, hkq⟩ := G.nonzero q
    obtain ⟨a, ha, hap⟩ := F.nonzero p
    obtain ⟨b, hb, hbq⟩ := F.nonzero q
    refine ⟨a.factorMul (g.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h a ha g hg,
      b.factorMul (k.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h b hb k hk, ?_⟩
    simp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply, hgq, mul_zero, zero_mul]
    exact mul_ne_zero (mul_ne_zero hap hgp) (mul_ne_zero hbq hkq)
  · refine ⟨s.factorMul (g.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h s hs g hg,
      t.factorMul (g.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h t ht g hg, ?_⟩
    apply sub_ne_zero.mp
    have he :
        s.factorMul (g.castDegree h) p * t.factorMul (g.castDegree h) q -
          s.factorMul (g.castDegree h) q * t.factorMul (g.castDegree h) p =
        (g p * g q) * (s p * t q - s q * t p) := by
      simp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hgp hgq) (sub_ne_zero.mpr hdet)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_right (p v : Φ.space) (hG : G.Detects p v) :
    (F.factorMul G h).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hG
  obtain ⟨g, hg, hgp⟩ := F.nonzero p
  refine ⟨g.factorMul (s.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h g hg s hs,
    g.factorMul (t.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h g hg t ht, ?_, ?_⟩
  · rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply]
    exact mul_ne_zero hgp hsp
  · apply sub_ne_zero.mp
    change Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.wronskian (g.factorMul (s.castDegree h)) (g.factorMul (t.castDegree h)) p v ≠ 0
    rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_cast_coe, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_cast_coe,
      mul_comm (g : Φ.space → ℂ) (s : Φ.space → ℂ),
      mul_comm (g : Φ.space → ℂ) (t : Φ.space → ℂ),
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.wronskian_mul_right _ _ _ _ _ (s.differentiable p) (t.differentiable p) (g.differentiable p)]
    exact mul_ne_zero (pow_ne_zero 2 hgp) (sub_ne_zero.mpr hdet)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_right (p q : Φ.space) (hG : G.Separates p q) :
    (F.factorMul G h).Separates p q := by
  obtain ⟨s, hs, t, ht, hdet⟩ := hG
  obtain ⟨g, hg, hgp⟩ := F.nonzero p
  by_cases hgq : g q = 0
  · obtain ⟨k, hk, hkq⟩ := F.nonzero q
    obtain ⟨a, ha, hap⟩ := G.nonzero p
    obtain ⟨b, hb, hbq⟩ := G.nonzero q
    refine ⟨g.factorMul (a.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h g hg a ha,
      k.factorMul (b.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h k hk b hb, ?_⟩
    simp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply, hgq, zero_mul]
    exact mul_ne_zero (mul_ne_zero hgp hap) (mul_ne_zero hkq hbq)
  · refine ⟨g.factorMul (s.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h g hg s hs,
      g.factorMul (t.castDegree h), AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem F G h g hg t ht, ?_⟩
    apply sub_ne_zero.mp
    have he :
        g.factorMul (s.castDegree h) p * g.factorMul (t.castDegree h) q -
          g.factorMul (s.castDegree h) q * g.factorMul (t.castDegree h) p =
        (g p * g q) * (s p * t q - s q * t p) := by
      simp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hgp hgq) (sub_ne_zero.mpr hdet)

end

end OAI.RepresentationTheory.Theta.Geometric
