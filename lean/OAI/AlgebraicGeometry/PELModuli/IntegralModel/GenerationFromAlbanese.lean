import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberGeneration
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordBaseChange

/-! # Generation From Albanese -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-!
Generation of every geometric fiber of an actual spread of a complex Albanese
map. The generic word-surjectivity hypothesis has been eliminated: the proof
derives it from Albanese universality and the geometric fiber identifications.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem GenerationFromAlbanese.over_iso_surjective {B : Scheme} {X Y : Over B} (e : X ≅ Y) :
    Surjective e.hom.left :=
  inferInstanceAs (Surjective ((Over.forget B).mapIso e).hom)

/-- Any actual proper spread of a complex Albanese map generates every
geometric fiber with one fixed positive number of point differences.
The isomorphisms identify schemes and the group law; no cohomology or
generation comparison is assumed. -/
theorem GenerationFromAlbanese.uniform_generation_of_complex_albanese
    {B : Scheme} (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) [IsDominant c]
    {X A : Over B} [GrpObj A] [IsCommMonObj A]
    [IsProper X.hom] [IsProper A.hom] [Smooth A.hom]
    (a : X ⟶ A)
    (XC : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (AC : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eX : (Over.pullback c).obj X ≅ XC.toOver)
    (eA : (Over.pullback c).obj A ≅ AC.toOver) [IsMonHom eA.hom]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ XC.toOver) (aC : XC.toOver ⟶ AC.toOver)
    (hcompatible : (Over.pullback c).map a ≫ eA.hom = eX.hom ≫ aC)
    (hAlbanese : Albanese.IsAlbaneseMap XC.presentation x₀ AC aC) :
    ∃ n : ℕ, 0 < n ∧ ∀ t : Base.GeometricPoint B,
      Function.Surjective
        (fun z : Fin n → (Over.mk t.morphism ⟶ X) × (Over.mk t.morphism ⟶ X) =>
          ∑ i, (Additive.ofMul ((z i).1 ≫ a) - Additive.ofMul ((z i).2 ≫ a))) := by
  obtain ⟨n, hn, hword⟩ :=
    Albanese.albanese_finite_word_surjective XC.presentation x₀ AC aC hAlbanese
  let : Surjective (Albanese.Construction.ImageWords.wordMap XC.presentation AC aC n).left := hword
  have hwordC : Surjective (Words.DifferenceWords.map aC n).left := by
    rw [WordBaseChange.DifferenceWords.e07_map XC.presentation AC aC n]
    let : Surjective (eqToHom (WordBaseChange.DifferenceWords.e07_domain XC.presentation n)).left :=
      GenerationFromAlbanese.over_iso_surjective (eqToIso (WordBaseChange.DifferenceWords.e07_domain XC.presentation n))
    dsimp only [Over.comp_left]
    infer_instance
  let : Surjective (Words.DifferenceWords.map aC n).left := hwordC
  have hcomparison : (Over.pullback c).map (Words.DifferenceWords.map a n) ≫ eA.hom =
      (WordBaseChange.DifferenceWords.baseChangeDomain c X n).hom ≫
        (WordBaseChange.DifferenceWords.domainIso eX n).hom ≫ Words.DifferenceWords.map aC n := by
    rw [WordBaseChange.DifferenceWords.baseChange_map, Category.assoc,
      WordBaseChange.DifferenceWords.map_naturality _ _ _ _ hcompatible,
      WordBaseChange.DifferenceWords.domainIso_hom]
  have hgeneric : Surjective ((Over.pullback c).map (Words.DifferenceWords.map a n)).left := by
    have hsurj : Surjective
        (((Over.pullback c).map (Words.DifferenceWords.map a n) ≫ eA.hom) ≫ eA.inv).left := by
      rw [hcomparison]
      let : Surjective (WordBaseChange.DifferenceWords.baseChangeDomain c X n).hom.left :=
        GenerationFromAlbanese.over_iso_surjective _
      let : Surjective (WordBaseChange.DifferenceWords.domainIso eX n).hom.left := GenerationFromAlbanese.over_iso_surjective _
      let : Surjective eA.inv.left := GenerationFromAlbanese.over_iso_surjective eA.symm
      dsimp only [Over.comp_left]
      infer_instance
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hsurj
  exact ⟨n, hn, fun t => FiberGeneration.difference_sums_surjective_on_geometric_fibers
    c a n hgeneric t.field t.morphism⟩

theorem Components.ComponentAlbaneseData.uniform_generation_of_complex_albanese
    {B : Scheme} (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) [IsDominant c]
    {M : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData M r) (j : Fin r)
    [IsProper (D.S j).hom] [IsProper (D.A j).X.hom] [Smooth (D.A j).X.hom]
    (XC : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (AC : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eX : D.complexSurface c j ≅ XC.toOver)
    (eA : (Over.pullback c).obj (D.A j).X ≅ AC.toOver) [IsMonHom eA.hom]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ XC.toOver) (aC : XC.toOver ⟶ AC.toOver)
    (hcompatible : D.complexMap c j ≫ eA.hom = eX.hom ≫ aC)
    (hAlbanese : Albanese.IsAlbaneseMap XC.presentation x₀ AC aC) :
    ∃ n : ℕ, 0 < n ∧ ∀ t : Base.GeometricPoint B,
      Function.Surjective (D.sumOfDifferences j n t) :=
  GenerationFromAlbanese.uniform_generation_of_complex_albanese
    c (D.a j) XC AC eX eA x₀ aC hcompatible hAlbanese

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
