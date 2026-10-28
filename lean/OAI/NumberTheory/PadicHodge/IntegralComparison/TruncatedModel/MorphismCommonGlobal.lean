import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality

/-! # Morphism Common Global -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal

/-! The genuine common source cover computes original bounded
crystalline cohomology, and the actual geometric map preserves its
canonical global edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOpenPairs.source p k n u f₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOpenPairs.target p k n u f₂
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁

instance source_products (q : ℕ) (t : Fin (q + 1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) F₁ :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves F₁ (fun _ _ => rfl) (U ∘ t)

instance target_products (q : ℕ) (t : Fin (q + 1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) F₂ :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves F₂ (fun _ _ => rfl) (U ∘ t)

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] [CharP k p] in
theorem source_cover : iSup ((F₁).obj ∘ U) = ⊤ := by
  apply top_unique
  intro y _
  have hy : f₁ y ∈ ⨆ i, (MorphismCover.opens p k n u i).val := by
    rw [MorphismCover.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

def sourceSections := ((MorphismSectionMap.sourceSections p k n u f₁).mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex
def targetSections := ((MorphismSectionMap.targetSections p k n u f₂).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex

def sourceEdge := GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (sourceSections p k n u f₁ I₁)
  (MorphismGlobalCone.sourceGlobal p k n I₁) (MorphismGlobalCone.sourceCone p k n u f₁ I₁)
def targetEdge := GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (targetSections p k n u f₂ I₂)
  (MorphismGlobalCone.targetGlobal p k n I₂) (MorphismGlobalCone.targetCone p k n u f₂ I₂)

def geometricMap := GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U
  (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem naturality : targetEdge p k n u f₂ I₂ ≫ geometricMap p k n u v f₁ f₂ sq I₁ I₂ =
    MorphismGlobalCone.globalMap p k n v I₁ I₂ ≫ sourceEdge p k n u f₁ I₁ :=
  GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality U
    (MorphismGlobalCone.targetCone p k n u f₂ I₂)
    (MorphismGlobalCone.sourceCone p k n u f₁ I₁)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismGlobalCone.globalMap p k n v I₁ I₂)
    (MorphismGlobalCone.naturality p k n u v f₁ f₂ sq I₁ I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem source_quasiIso : QuasiIso (sourceEdge p k n u f₁ I₁) :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.quasiIso w₁ n I₁ F₁ U (source_cover p k n u f₁)

def sourceHomologyIso (i : ℕ) :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homologyIso w₁ n I₁ F₁ U (source_cover p k n u f₁) i

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem source_homology (i : ℕ) : HomologicalComplex.homologyMap (sourceEdge p k n u f₁ I₁) i ≫
    (sourceHomologyIso p k n u f₁ I₁ i).hom = (BoundedOpen.SectionGlobal.homologyIso w₁ n I₁ i).hom :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homology w₁ n I₁ F₁ U (source_cover p k n u f₁) i

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.Naturality

/-! The common-cover geometric map is the original bounded crystalline pullback after the canonical global edge, in every cohomological degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.targetEdge p k n u f₂ I₂
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂
local notation "c" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.globalMap p k n v I₁ I₂
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.sourceEdge p k n u f₁ I₁

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem homology (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫ HomologicalComplex.homologyMap b q ≫
      (sourceHomologyIso p k n u f₁ I₁ q).hom =
    (BoundedOpen.SectionGlobal.homologyIso w₂ n I₂ q).hom ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n q) := by
  have h : HomologicalComplex.homologyMap a q ≫ HomologicalComplex.homologyMap b q =
      HomologicalComplex.homologyMap c q ≫ HomologicalComplex.homologyMap d q :=
    (HomologicalComplex.homologyMap_comp a b q).symm.trans
      ((congrArg (fun z => HomologicalComplex.homologyMap z q)
        (naturality p k n u v f₁ f₂ sq I₁ I₂)).trans
          (HomologicalComplex.homologyMap_comp c d q))
  rw [← Category.assoc, h, Category.assoc,
    source_homology]
  exact GeometricComparison.Bounded.OpenCohomology.BoundedGeometricOpenCohomology.homology v.left
    (MorphismData.Frames.ambient_over p k v) n I₂ I₁ q

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.Naturality

end

end OAI
