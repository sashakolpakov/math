import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafGluing

/-! # Open Ideal Sheaf Uniqueness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafUniqueness.Construction

noncomputable section

/-! Uniqueness of gluing on an affine open cover, for independence of chart choices. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Ideal sheaves agreeing on an affine open cover are equal, expressed
using actual open immersions and their ideal-sheaf pullbacks. -/
theorem idealSheaf_eq_of_open_affine_restrictions
    {X : Scheme.{u}} {ι : Type v} (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsAffine (U i)] [∀ i, IsOpenImmersion (j i)]
    (hcover : ⨆ i, (j i).opensRange = ⊤) (I L : X.IdealSheafData)
    (hlocal : ∀ i, I.comap (j i) = L.comap (j i)) : I = L := by
  let W : ι → X.affineOpens := fun i =>
    ⟨(j i) ''ᵁ ⊤, (isAffineOpen_top (U i)).image_of_isOpenImmersion (j i)⟩
  have hW : ⨆ i, (W i).1 = ⊤ := by
    simpa only [W, Scheme.Hom.image_top_eq_opensRange] using hcover
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top W hW
  intro i
  let V : (U i).affineOpens := ⟨⊤, isAffineOpen_top (U i)⟩
  have he := congrArg (fun Q : (U i).IdealSheafData => Q.ideal V) (hlocal i)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at he
  have hsurj : Function.Surjective ((j i).appIso (⊤ : (U i).Opens)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso ((j i).appIso (⊤ : (U i).Opens)).inv).2
  exact Ideal.comap_injective_of_surjective _ hsurj he

/-- Compatible data on a finite affine open cover determine exactly one
global ideal sheaf, constructed by the proved finite intersection formula. -/
theorem existsUnique_idealSheaf_of_finite_affine_cover
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsAffine (U i)] [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hcover : ⨆ i, (j i).opensRange = ⊤) (J : ∀ i, (U i).IdealSheafData)
    (hcompat : ∀ a b : ι,
      (J a).comap (pullback.fst (j a) (j b)) =
        (J b).comap (pullback.snd (j a) (j b))) :
    ∃! I : X.IdealSheafData, ∀ a, I.comap (j a) = J a := by
  have hglue := OpenIdealSheafGluing.Construction.gluedFiniteOpenIdealSheaf_restrict U j J hcompat
  refine ⟨OpenIdealSheafGluing.Construction.gluedFiniteOpenIdealSheaf U j J, hglue, ?_⟩
  intro I hI
  exact idealSheaf_eq_of_open_affine_restrictions U j hcover I (OpenIdealSheafGluing.Construction.gluedFiniteOpenIdealSheaf U j J)
    (fun a => (hI a).trans (hglue a).symm)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafUniqueness.Construction
