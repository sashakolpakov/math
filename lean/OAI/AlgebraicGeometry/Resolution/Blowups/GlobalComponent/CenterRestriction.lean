import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center

/-! # Center Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

section

/-! Independence of the actual global component center from its finite affine atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

def ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.append (A B : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n where
  indices := A.indices ⊕ B.indices
  finite := inferInstance
  rings := Sum.elim A.rings B.rings
  algebra := by intro i; cases i with | inl a => exact A.algebra a | inr b => exact B.algebra b
  rational := by intro i; cases i with | inl a => exact A.rational a | inr b => exact B.rational b
  smooth := by intro i; cases i with | inl a => exact A.smooth a | inr b => exact B.smooth b
  map := by intro i; cases i with | inl a => exact A.map a | inr b => exact B.map b
  isOpenImmersion := by intro i; cases i with | inl a => exact A.isOpenImmersion a | inr b => exact B.isOpenImmersion b
  quasiCompact := by intro i; cases i with | inl a => exact A.quasiCompact a | inr b => exact B.quasiCompact b
  ground := by intro i; cases i with | inl a => exact A.ground a | inr b => exact B.ground b
  cover := by
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ ⨆ a, (A.map a).opensRange := by rw [A.cover]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inl a, ha⟩
  ideals := by intro i; cases i with | inl a => exact A.ideals a | inr b => exact B.ideals b
  ideal_eq := by intro i; cases i with | inl a => exact A.ideal_eq a | inr b => exact B.ideal_eq b
  choice := by intro i; cases i with | inl a => exact A.choice a | inr b => exact B.choice b

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_eq (A B : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : A.center = B.center := by
  let C := A.append B
  have hA : C.center = A.center := A.existsUnique_center.choose_spec.2 C.center
    (fun a => C.center_restrict (Sum.inl a))
  have hB : C.center = B.center := B.existsUnique_center.choose_spec.2 C.center
    (fun b => C.center_restrict (Sum.inr b))
  exact hA.symm.trans hB

end

section

/-! The canonical global component center agrees with every additional smooth affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

def ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.insertChart (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (R : CommRingCat)
    [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (L : Ideal R) (hL : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L)
    (C : Component.CenterChoice.Construction.ComponentCenterChoice ℂ R L n) : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n where
  indices := A.indices ⊕ Unit
  finite := inferInstance
  rings := Sum.elim A.rings (fun _ => R)
  algebra := by intro i; cases i with | inl a => exact A.algebra a | inr _ => exact inferInstanceAs (Algebra ℂ R)
  rational := by intro i; cases i with | inl a => exact A.rational a | inr _ => exact inferInstanceAs (Algebra ℚ R)
  smooth := by intro i; cases i with | inl a => exact A.smooth a | inr _ => exact inferInstanceAs (Algebra.Smooth ℂ R)
  map := by intro i; cases i with | inl a => exact A.map a | inr _ => exact j
  isOpenImmersion := by intro i; cases i with | inl a => exact A.isOpenImmersion a | inr _ => exact inferInstanceAs (IsOpenImmersion j)
  quasiCompact := by intro i; cases i with | inl a => exact A.quasiCompact a | inr _ => exact inferInstanceAs (QuasiCompact j)
  ground := by intro i; cases i with | inl a => exact A.ground a | inr _ => exact hj
  cover := by
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ ⨆ a, (A.map a).opensRange := by rw [A.cover]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inl a, ha⟩
  ideals := by intro i; cases i with | inl a => exact A.ideals a | inr _ => exact L
  ideal_eq := by intro i; cases i with | inl a => exact A.ideal_eq a | inr _ => exact hL
  choice := by intro i; cases i with | inl a => exact A.choice a | inr _ => exact C

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_restrict_any (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (R : CommRingCat)
    [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (L : Ideal R) (hL : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L)
    (C : Component.CenterChoice.Construction.ComponentCenterChoice ℂ R L n) :
    A.center.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel C.center := by
  let B := A.insertChart R j hj L hL C
  rw [A.center_eq B]
  exact B.center_restrict (Sum.inr ())

end

/-! The canonical global component center has its proved local formula on every étale affine chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_restrict_etale (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (R : CommRingCat)
    [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (L : Ideal R) (hL : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L)
    (C : Component.CenterChoice.Construction.ComponentCenterChoice ℂ R L n) : A.center.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel C.center := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  have hcover : (⨆ i, (pullback.snd (A.map i) j).opensRange) = ⊤ := by
    simp_rw [Scheme.Hom.opensRange_pullbackSnd]
    rw [← Scheme.Hom.preimage_iSup, A.cover, Scheme.Hom.preimage_top]
  let 𝒰 : (Spec R).OpenCover := Scheme.Cover.mkOfCovers A.indices
    (fun i => pullback (A.map i) j) (fun i => pullback.snd (A.map i) j)
    (by
      intro x
      have hx : x ∈ ⨆ i, (pullback.snd (A.map i) j).opensRange := by rw [hcover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx)
    (fun _ => inferInstance)
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ 𝒰
  intro i
  change A.indices at i
  change (A.center.comap j).comap (pullback.snd (A.map i) j) =
    (Affine.QuotientKernel.Construction.affineQuotientKernel C.center).comap (pullback.snd (A.map i) j)
  rw [← Scheme.IdealSheafData.comap_comp, ← pullback.condition,
    Scheme.IdealSheafData.comap_comp, A.center_restrict i]
  apply GlobalCoefficient.ComponentGluing.Construction.idealSheaf_eq_of_fromSpec
  intro W
  let P := pullback (A.map i) j
  let S := Γ(P, W)
  let u : Spec (.of S) ⟶ Spec (A.rings i) := W.2.fromSpec ≫ pullback.fst (A.map i) j
  let v : Spec (.of S) ⟶ Spec R := W.2.fromSpec ≫ pullback.snd (A.map i) j
  let φ : A.rings i →+* S := (Spec.preimage u).hom
  let ψ : R →+* S := (Spec.preimage v).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = u := Spec.map_preimage u
  have hψ : Spec.map (CommRingCat.ofHom ψ) = v := Spec.map_preimage v
  have hcomm : u ≫ A.map i = v ≫ j := by
    dsimp only [u, v]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hbase : φ.comp (algebraMap ℂ (A.rings i)) = ψ.comp (algebraMap ℂ R) := by
    have he : CommRingCat.ofHom (φ.comp (algebraMap ℂ (A.rings i))) =
        CommRingCat.ofHom (ψ.comp (algebraMap ℂ R)) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap ℂ (A.rings i)) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ R) ≫ CommRingCat.ofHom ψ)
      rw [Spec.map_comp, Spec.map_comp, hφ, hψ]
      change u ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (A.rings i) = v ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R
      rw [← A.ground i, ← hj]
      simpa only [Category.assoc] using congrArg (fun m => m ≫ f) hcomm
    exact congrArg CommRingCat.Hom.hom he
  let : Algebra ℂ S := (φ.comp (algebraMap ℂ (A.rings i))).toAlgebra
  let φₖ : A.rings i →ₐ[ℂ] S := { __ := φ, commutes' := fun _ => rfl }
  let ψₖ : R →ₐ[ℂ] S := { __ := ψ, commutes' := fun c => (RingHom.congr_fun hbase c).symm }
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  have hφe : φₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale u)
  have hψe : ψₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale v)
  have hJL : (A.ideals i).map φ = L.map ψ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hφ, hψ,
      ← A.ideal_eq i, ← hL, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hc := Component.CenterChoice.Construction.ComponentCenterChoice.center_eq_on_common_refinement φₖ ψₖ hφe hψe hJL (A.choice i) C
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  change (Affine.QuotientKernel.Construction.affineQuotientKernel (A.choice i).center).comap u = (Affine.QuotientKernel.Construction.affineQuotientKernel C.center).comap v
  rw [← hφ, ← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
