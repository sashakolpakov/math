import OAI.ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws

/-! # Family Endomorphism Charts -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints

/-!
Regard the given algebraic family endomorphism as an actual map on the
complex total scheme and on each literal base-change fiber. The fiber
inclusion square and preservation of the actual identity section are proved.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)

def familyEndomorphism (k : G.scheme ⟶ G.scheme) : AbelianFamilyPoints.FamilyPoints.total S G ⟶ AbelianFamilyPoints.FamilyPoints.total S G :=
  Over.homMk k.left (by
    change k.left ≫ (G.scheme.hom ≫ S.hom) = G.scheme.hom ≫ S.hom
    rw [← Category.assoc, k.w])

def fiberEndomorphism (k : G.scheme ⟶ G.scheme) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    (G.pullback s.left).scheme ⟶ (G.pullback s.left).scheme :=
  (Over.pullback s.left).map k

theorem fiberEndomorphism_group (k : G.scheme ⟶ G.scheme) [IsMonHom k] (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    IsMonHom (fiberEndomorphism S G k s) := by
  let : MonObj ((Over.pullback s.left).obj G.scheme) :=
    Functor.monObjObj (F := Over.pullback s.left) G.scheme
  change IsMonHom ((Over.pullback s.left).map k)
  infer_instance

theorem familyEndomorphism_identity (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    AbelianFamilyPoints.FamilyPoints.identitySection S G ≫ familyEndomorphism S G k = AbelianFamilyPoints.FamilyPoints.identitySection S G := by
  apply Over.OverMorphism.ext
  change ((1 : Over.mk (𝟙 S.left) ⟶ G.scheme) ≫ k).left =
    (1 : Over.mk (𝟙 S.left) ⟶ G.scheme).left
  rw [MonObj.one_comp]

theorem fiberEndomorphism_inclusion (k : G.scheme ⟶ G.scheme) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    fiberEndomorphism S G k s ≫ AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s =
      AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s ≫ familyEndomorphism S G k := by
  apply Over.OverMorphism.ext
  change ((Over.pullback s.left).map k).left ≫ CategoryTheory.Limits.pullback.fst G.scheme.hom s.left =
    CategoryTheory.Limits.pullback.fst G.scheme.hom s.left ≫ k.left
  simp only [Over.pullback_map_left, CategoryTheory.Limits.pullback.lift_fst]

end ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints

namespace ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.RelativeCharts

/-!
Write the actual family endomorphism in the constructed relative charts.
Its coordinate expression is analytic on a constructed open neighborhood
of the identity section's central point, by regular-function evaluation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.CategoryTheory.MonObj

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {σ : A →ₐ[ℂ] R}

def familyEndomorphismCoordinates
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (k : G.scheme ⟶ G.scheme)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ) : F × E → F × E :=
  fun z => AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyPoints.familyEndomorphism S G k)
      ((AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).symm z))

theorem exists_analytic_familyEndomorphism_coordinates
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (k : G.scheme ⟶ G.scheme) [IsMonHom k]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x ≫
        AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) :
    ∃ D : Set (F × E), IsOpen D ∧
      (N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), (0 : E)) ∈ D ∧
      D ⊆ N.charts.total.target ∧
      ContDiffOn ℂ ω (familyEndomorphismCoordinates G k i N) D ∧
      ∀ z ∈ D,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyPoints.familyEndomorphism S G k)
          ((AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).symm z) ∈
            (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source := by
  let K := FamilyPoints.familyEndomorphism S G k
  let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  let q := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x
  have hfix : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K q = q := by
    change q ≫ K = q
    calc
      q ≫ K = ((q ≫ AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) ≫ K :=
        congrArg (fun z => z ≫ K) hx
      _ = (q ≫ AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G := by
        rw [Category.assoc, FamilyPoints.familyEndomorphism_identity]
      _ = q := hx.symm
  let f := fun z : F × E => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) (i ≫ K)
    (N.charts.total.symm z)
  let D := N.charts.total.target ∩ f ⁻¹' e.source
  have hD : IsOpen D := AnalyticSchemeFamilies.Abelian.RelativeCharts.isOpen_schemeImage_affineChart_domain
    (CommAlgCat.of ℂ A) (CommAlgCat.of ℂ A) (i ≫ K) i N.charts.total
    N.charts.total.symm N.charts.total.target N.charts.total.open_target N.charts.regularTotal
  have hinv₀ : N.charts.total.symm (q₀, 0) = x := by
    rw [← N.center_coordinates, N.charts.total.left_inv N.charts.point]
  have hpoint (z : F × E) : f z = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K (e.symm z) :=
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp (CommAlgCat.of ℂ A) i K (N.charts.total.symm z)
  have hcenter : (q₀, (0 : E)) ∈ D := by
    constructor
    · have h := N.charts.total.map_source N.charts.point
      rw [N.center_coordinates] at h
      exact h
    · change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) (i ≫ K)
        (N.charts.total.symm (q₀, 0)) ∈ e.source
      rw [hinv₀, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp]
      change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K q ∈ e.source
      rw [hfix]
      exact ⟨x, N.charts.point, rfl⟩
  refine ⟨D, hD, hcenter, inter_subset_left, ?_, ?_⟩
  · have h := AnalyticSchemeFamilies.Abelian.RelativeCharts.contDiffOn_schemeImage_in_affineChart
      (CommAlgCat.of ℂ A) (CommAlgCat.of ℂ A) (i ≫ K) i N.charts.total N.forwardTotal
      N.charts.total.symm N.charts.total.target N.charts.total.open_target N.charts.regularTotal
    apply h.congr
    intro z _
    exact congrArg e (hpoint z).symm
  · intro z hz
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K (e.symm z) ∈ e.source
    rw [← hpoint]
    exact hz.2

end ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.RelativeCharts

end

end OAI
