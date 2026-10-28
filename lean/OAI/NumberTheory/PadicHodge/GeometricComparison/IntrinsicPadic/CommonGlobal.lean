import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality

/-! # Common Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonGlobal.IntrinsicPadicGeometricCommonGlobal

noncomputable section

/-! The genuine common source cover computes original bounded
crystalline cohomology, and the actual geometric map preserves its
canonical global edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "F₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenPairs.IntrinsicPadicGeometricOpenPairs.source p u f₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenPairs.IntrinsicPadicGeometricOpenPairs.target p u f₂
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁

instance source_products (q : ℕ) (t : Fin (q + 1) → Cover.IntrinsicPadicGeometricCover.Index p u) :
    PreservesLimit (Discrete.functor (U ∘ t)) F₁ :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves F₁ (fun _ _ => rfl) (U ∘ t)

instance target_products (q : ℕ) (t : Fin (q + 1) → Cover.IntrinsicPadicGeometricCover.Index p u) :
    PreservesLimit (Discrete.functor (U ∘ t)) F₂ :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves F₂ (fun _ _ => rfl) (U ∘ t)

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_cover : iSup ((F₁).obj ∘ U) = ⊤ := by
  apply top_unique
  intro y _
  have hy : f₁ y ∈ ⨆ i, (Cover.IntrinsicPadicGeometricCover.opens p u i).val := by
    rw [Cover.IntrinsicPadicGeometricCover.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

def sourceSections := ((SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n).mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex
def targetSections := ((SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex

def sourceEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (sourceSections p u f₁ n I₁)
  (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁) (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceCone p u f₁ n I₁)
def targetEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (targetSections p u f₂ n I₂)
  (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂) (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetCone p u f₂ n I₂)

def geometricMap := CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U
  (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem naturality : targetEdge p u f₂ n I₂ ≫ geometricMap p u v f₁ f₂ hsquare n I₁ I₂ =
    GlobalCone.IntrinsicPadicGeometricGlobalCone.globalMap p v n I₁ I₂ ≫ sourceEdge p u f₁ n I₁ :=
  CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality U
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetCone p u f₂ n I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceCone p u f₁ n I₁)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.globalMap p v n I₁ I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.naturality p u v f₁ f₂ hsquare n I₁ I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_quasiIso : QuasiIso (sourceEdge p u f₁ n I₁) :=
  Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.quasiIso w₁ n I₁ F₁ U (source_cover p u f₁)

def sourceHomologyIso (i : ℕ) :=
  Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homologyIso w₁ n I₁ F₁ U (source_cover p u f₁) i

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_homology (i : ℕ) : HomologicalComplex.homologyMap (sourceEdge p u f₁ n I₁) i ≫
    (sourceHomologyIso p u f₁ n I₁ i).hom = (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₁ n I₁ i).hom :=
  Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homology w₁ n I₁ F₁ U (source_cover p u f₁) i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonGlobal.IntrinsicPadicGeometricCommonGlobal
