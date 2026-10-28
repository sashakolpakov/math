import OAI.RepresentationTheory.Theta.Geometric.AutomorphyFactorOperations

/-! # Automorphic Family Products -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Basepoint-free theta families pull back along linear period maps
and multiply across automorphy factors without changing their common degree. -/

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData} {J K : Φ.AutomorphyFactor}

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.comap f hf) := by
  classical
  exact
    { degree := F.degree
      sections := F.sections.image (fun s => s.comap f hf)
      nonzero := fun z => by
        obtain ⟨s, hs, hsz⟩ := F.nonzero (f z)
        exact ⟨s.comap f hf, Finset.mem_image.mpr ⟨s, hs, rfl⟩, hsz⟩ }

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_degree (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice) :
    (F.comap f hf).degree = F.degree := rfl

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family K) (h : G.degree = F.degree) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.mul K) := by
  classical
  exact
    { degree := F.degree
      sections := (F.sections ×ˢ G.sections).image (fun st => st.1.factorMul (st.2.castDegree h))
      nonzero := fun z => by
        obtain ⟨s, hs, hsz⟩ := F.nonzero z
        obtain ⟨t, ht, htz⟩ := G.nonzero z
        refine ⟨s.factorMul (t.castDegree h), Finset.mem_image.mpr
          ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
        rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply]
        exact mul_ne_zero hsz htz }

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_degree (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family K) (h : G.degree = F.degree) :
    (F.factorMul G h).degree = F.degree := rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family K) (h : G.degree = F.degree)
    (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (hs : s ∈ F.sections)
    (t : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section K G.degree) (ht : t ∈ G.sections) :
    s.factorMul (t.castDegree h) ∈ (F.factorMul G h).sections := by
  classical
  exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩

end

/-! A pulled-back theta family detects precisely the point and tangent
separation supplied by its linear period map. -/

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.comap_fderiv {n : ℕ} (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (p v : Ψ.space) :
    fderiv ℂ (s.comap f hf) p v = fderiv ℂ s (f p) (f v) :=
  congrArg (fun d : Ψ.space →L[ℂ] ℂ => d v)
    (((s.differentiable (f p)).hasFDerivAt.comp p f.hasFDerivAt).fderiv)

variable (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (hs : s ∈ F.sections) :
    s.comap f hf ∈ (F.comap f hf).sections := by
  classical
  exact Finset.mem_image.mpr ⟨s, hs, rfl⟩

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_separates (p q : Ψ.space) (h : F.Separates (f p) (f q)) :
    (F.comap f hf).Separates p q := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s.comap f hf, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem f hf F s hs, t.comap f hf, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem f hf F t ht, hst⟩

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_detects (p v : Ψ.space) (h : F.Detects (f p) (f v)) :
    (F.comap f hf).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hst⟩ := h
  refine ⟨s.comap f hf, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem f hf F s hs, t.comap f hf, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem f hf F t ht, hsp, ?_⟩
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.comap_fderiv, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.comap_fderiv]
  exact hst

end

end OAI.RepresentationTheory.Theta.Geometric
