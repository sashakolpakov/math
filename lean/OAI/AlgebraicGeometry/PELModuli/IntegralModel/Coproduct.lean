import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent

/-! # Coproduct -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

noncomputable section

/-!
Disjoint scheme decompositions and their pullbacks. The covers and disjointness
are derived from the coproduct isomorphism, rather than assumed on its fibers.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme} {r : ℕ} (U : Fin r → Over B)

def underlyingCoproductIso : (∐ U).left ≅ ∐ (fun i => (U i).left) :=
  PreservesCoproduct.iso (Over.forget B) U

@[reassoc (attr := simp)] theorem underlyingCoproductIso_ι (i : Fin r) :
    Sigma.ι (fun k => (U k).left) i ≫ (underlyingCoproductIso U).inv =
      (Sigma.ι U i).left := by
  exact ι_comp_sigmaComparison (Over.forget B) U i

def decompositionSchemeIso {M : Over B} (e : (∐ U) ≅ M) :
    (∐ fun i => (U i).left) ≅ M.left :=
  (underlyingCoproductIso U).symm ≪≫ (Over.forget B).mapIso e

@[reassoc (attr := simp)] theorem decompositionSchemeIso_ι {M : Over B}
    (e : (∐ U) ≅ M) (i : Fin r) :
    Sigma.ι (fun k => (U k).left) i ≫ (decompositionSchemeIso U e).hom =
      (Sigma.ι U i ≫ e.hom).left := by
  change Sigma.ι (fun k => (U k).left) i ≫
    ((underlyingCoproductIso U).inv ≫ e.hom.left) =
      (Sigma.ι U i).left ≫ e.hom.left
  rw [← Category.assoc, underlyingCoproductIso_ι]

def decompositionHomeomorph {M : Over B} (e : (∐ U) ≅ M) :
    (Σ i, (U i).left) ≃ₜ M.left :=
  (sigmaMk (fun i => (U i).left)).trans (decompositionSchemeIso U e).hom.homeomorph

@[simp] theorem decompositionHomeomorph_apply {M : Over B} (e : (∐ U) ≅ M)
    (i : Fin r) (x : (U i).left) :
    decompositionHomeomorph U e ⟨i, x⟩ = (Sigma.ι U i ≫ e.hom).left x := by
  change (decompositionSchemeIso U e).hom (sigmaMk _ ⟨i, x⟩) = _
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, decompositionSchemeIso_ι]

theorem decomposition_inclusion_open {M : Over B} (e : (∐ U) ≅ M) (i : Fin r) :
    IsOpenImmersion (Sigma.ι U i ≫ e.hom).left := by
  rw [← decompositionSchemeIso_ι U e i]
  infer_instance

theorem decomposition_cover {M : Over B} (e : (∐ U) ≅ M) (x : M.left) :
    ∃ i, x ∈ Set.range (Sigma.ι U i ≫ e.hom).left := by
  obtain ⟨⟨i, y⟩, hy⟩ := (decompositionHomeomorph U e).surjective x
  exact ⟨i, y, (decompositionHomeomorph_apply U e i y).symm.trans hy⟩

theorem decomposition_disjoint {M : Over B} (e : (∐ U) ≅ M) :
    Pairwise (fun i j => Disjoint (Set.range (Sigma.ι U i ≫ e.hom).left)
      (Set.range (Sigma.ι U j ≫ e.hom).left)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy⟩ ⟨z, hz⟩
  apply hij
  have hpoints : (⟨i, y⟩ : Σ k, (U k).left) = ⟨j, z⟩ := by
    apply (decompositionHomeomorph U e).injective
    simpa only [decompositionHomeomorph_apply] using hy.trans hz.symm
  exact congrArg Sigma.fst hpoints

theorem baseChange_map_range {C : Scheme} (g : C ⟶ B) {X Y : Over B} (f : X ⟶ Y) :
    Set.range ((Over.pullback g).map f).left =
      pullback.fst Y.hom g ⁻¹' Set.range f.left := by
  have hf : X.hom ≫ 𝟙 B = f.left ≫ Y.hom := by simp
  have hg : g ≫ 𝟙 B = 𝟙 C ≫ g := by simp
  have heq : ((Over.pullback g).map f).left =
      pullback.map X.hom g Y.hom g f.left (𝟙 C) (𝟙 B) hf hg := by
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.map, pullback.lift_fst]
    · simp only [Over.pullback_map_left, pullback.map, pullback.lift_snd, Category.comp_id]
  rw [heq, Scheme.Pullback.range_map]
  simp

theorem baseChange_inclusion_open {C : Scheme} (g : C ⟶ B) {X Y : Over B}
    (f : X ⟶ Y) [IsOpenImmersion f.left] :
    IsOpenImmersion ((Over.pullback g).map f).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (Specialization.base_change_square g f) inferInstance

theorem baseChange_decomposition_cover {C : Scheme} (g : C ⟶ B)
    {M : Over B} (e : (∐ U) ≅ M) (x : ((Over.pullback g).obj M).left) :
    ∃ i, x ∈ Set.range ((Over.pullback g).map (Sigma.ι U i ≫ e.hom)).left := by
  obtain ⟨i, hi⟩ := decomposition_cover U e (pullback.fst M.hom g x)
  exact ⟨i, by rw [baseChange_map_range]; exact hi⟩

theorem baseChange_decomposition_disjoint {C : Scheme} (g : C ⟶ B)
    {M : Over B} (e : (∐ U) ≅ M) :
    Pairwise (fun i j =>
      Disjoint (Set.range ((Over.pullback g).map (Sigma.ι U i ≫ e.hom)).left)
        (Set.range ((Over.pullback g).map (Sigma.ι U j ≫ e.hom)).left)) := by
  intro i j hij
  rw [baseChange_map_range, baseChange_map_range]
  exact (decomposition_disjoint U e hij).preimage _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct
