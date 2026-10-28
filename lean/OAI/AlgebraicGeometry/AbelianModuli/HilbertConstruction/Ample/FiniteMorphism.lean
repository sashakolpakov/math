import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Finite Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An ample line bundle yields an affine projective-space morphism, finite for proper schemes
over an affine base. The construction includes empty schemes and makes no moduli claim. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} {L : Line.Bundles.LineBundle X}

/-- An ample line bundle has a positive power with a nonempty finite indexing set of sections
whose affine nonvanishing opens cover, including when the scheme itself is empty. -/
theorem Line.Bundles.LineBundle.IsAmple.projective_section_family (hL : L.IsAmple) :
    ∃ (d : ℕ) (_ : 0 < d) (n : ℕ)
      (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf)),
      (∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) ∧
        ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)) := by
  obtain ⟨d, hd, k, s, ha, hs⟩ := hL.finite_common_power_cover
  let t : Fin (k + 1) → (Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf) := Fin.cases 0 s
  refine ⟨d, hd, k, t, fun x => ?_, fun i => ?_⟩
  · obtain ⟨i, hi⟩ := hs x
    exact ⟨i.succ, hi⟩
  · refine Fin.cases ?_ (fun j => ha j) i
    change IsAffineOpen (Ample.LineBundles.sectionNonvanishing (0 : Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf))
    rw [Line.Bundles.LineBundle.sectionNonvanishing_zero]
    exact isAffineOpen_bot X

/-- An ample line bundle yields an affine morphism to projective space with the prescribed base map. -/
theorem Line.Bundles.LineBundle.IsAmple.exists_affine_projective_morphism (hL : L.IsAmple) (f : X ⟶ S) :
    ∃ (n : ℕ) (a : X ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left),
      IsAffineHom a ∧ a ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom = f ≫ S.toSpecΓ := by
  obtain ⟨d, _hd, n, s, hs, ha⟩ := hL.projective_section_family
  exact ⟨n, SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs, Affine.SectionMorphism.sectionAbsoluteMorphism_affine f s hs ha,
    SectionsProjectiveMorphism.sectionAbsoluteMorphism_over f s hs⟩

/-- Over an affine base, a proper scheme carrying an ample line bundle admits a finite
morphism to projective space, constructed from sections of a positive power. -/
theorem Line.Bundles.LineBundle.IsAmple.exists_finite_projective_morphism (hL : L.IsAmple)
    (f : X ⟶ S) [IsProper f] [IsAffine S] :
    ∃ (n : ℕ) (a : Over.mk f ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n), IsFinite a.left := by
  obtain ⟨d, _hd, n, s, hs, ha⟩ := hL.projective_section_family
  let a := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : a.left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := pullback.lift_fst _ _ _
  have : IsFinite (a.left ≫ p) := hp.symm ▸ Affine.SectionMorphism.sectionAbsoluteMorphism_finite f s hs ha
  have : IsIso p := inferInstanceAs
    (IsIso (pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  exact ⟨n, a, IsFinite.of_comp a.left p⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
