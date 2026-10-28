import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Fiber Group Laws -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws.Abelian.FamilyPoints

/-!
The actual scheme-fiber inclusion identifies the given fiber group law
with the relative family multiplication. These identities tie the local
product-coordinate law to the genuine native group structure on each fiber.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
  (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

/-- The unit of the actual base-change fiber maps to the given identity
section at its actual base point. -/
theorem fiberInclusion_one :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)
        (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) =
      s ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G := by
  let e := G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
  have h := congrArg
    (fun u : G.Points ((Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) => u.left)
    (e.map_one)
  change (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme).left ≫
      CategoryTheory.Limits.pullback.fst G.scheme.hom s.left =
    (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ s.left) ≫ η[G.scheme].left at h
  rw [Category.id_comp] at h
  apply Over.OverMorphism.ext
  change (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme).left ≫
    CategoryTheory.Limits.pullback.fst G.scheme.hom s.left =
      s.left ≫ (𝟙 S.left ≫ η[G.scheme].left)
  rw [Category.id_comp]
  exact h

/-- Actual multiplication in the fiber agrees with multiplication of
the two relative points under the genuine fiber inclusion. -/
theorem fiberInclusion_mul
    (u v : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (u * v) =
      LocalizedFamily.Abelian.FamilyPoints.multiplyAlong G s
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) u)
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) v)
        (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph (AbelianFamilyPoints.FamilyPoints.projection S G) s u).property
        (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph (AbelianFamilyPoints.FamilyPoints.projection S G) s v).property := by
  let e := G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
  have h := congrArg
    (fun w : G.Points ((Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) => w.left)
    (e.map_mul u v)
  apply Over.OverMorphism.ext
  exact h

end ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws.Abelian.FamilyPoints

namespace ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws

/-!
Compare the actual affine tensor-product multiplication with the given
group law on each literal scheme fiber. Consequently its local coordinate
formula is the multiplication formula used by the native exponential ODE.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff TensorProduct _root_.CategoryTheory.MonObj

namespace Abelian.FamilyPoints

theorem multiplyAlong_congr {S T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) {q q' : T ⟶ S}
    {l l' r r' : T ⟶ AbelianFamilyPoints.FamilyPoints.total S G}
    (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S G = q) (hr : r ≫ AbelianFamilyPoints.FamilyPoints.projection S G = q)
    (hl' : l' ≫ AbelianFamilyPoints.FamilyPoints.projection S G = q') (hr' : r' ≫ AbelianFamilyPoints.FamilyPoints.projection S G = q')
    (hq : q = q') (hleft : l = l') (hright : r = r') :
    LocalizedFamily.Abelian.FamilyPoints.multiplyAlong G q l r hl hr = LocalizedFamily.Abelian.FamilyPoints.multiplyAlong G q' l' r' hl' hr' := by
  subst q'
  subst l'
  subst r'
  rfl

end Abelian.FamilyPoints

namespace Abelian.RelativeCharts

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}

/-- Evaluation of the genuine affine family multiplication is exactly
the genuine multiplication of the corresponding native fiber points. -/
theorem affineFamilyMultiplication_fiber_points
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G)
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (u v : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme)
    (w : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A))
    (hl : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i
      (w.comp Algebra.TensorProduct.includeLeft) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) u)
    (hr : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i
      (w.comp ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ)) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) v) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
      (LocalizedFamily.Abelian.RelativeCharts.affineFamilyMultiplication G b i hi) w =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (u * v) := by
  let k := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (A ⊗[R] A) w
  let l := LocalizedFamily.Abelian.RelativeCharts.tensorLeft (R := R) (A := A) ≫ i
  let r := LocalizedFamily.Abelian.RelativeCharts.tensorRight (R := R) (A := A) ≫ i
  have hleft : k ≫ l =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) u :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap (CommAlgCat.of ℂ A)
      (CommAlgCat.of ℂ (A ⊗[R] A)) Algebra.TensorProduct.includeLeft i w).trans hl
  have hright : k ≫ r =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) v :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap (CommAlgCat.of ℂ A)
      (CommAlgCat.of ℂ (A ⊗[R] A))
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ) i w).trans hr
  have hbase : k ≫ (l ≫ AbelianFamilyPoints.FamilyPoints.projection S G) = s := by
    rw [← Category.assoc, hleft]
    exact (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph (AbelianFamilyPoints.FamilyPoints.projection S G) s u).property
  unfold LocalizedFamily.Abelian.RelativeCharts.affineFamilyMultiplication
  change k ≫ LocalizedFamily.Abelian.FamilyPoints.multiplyAlong _ _ _ _ _ _ = _
  rw [LocalizedFamily.Abelian.FamilyPoints.multiplyAlong_comp]
  change LocalizedFamily.Abelian.FamilyPoints.multiplyAlong G (k ≫ (l ≫ AbelianFamilyPoints.FamilyPoints.projection S G))
    (k ≫ l) (k ≫ r) _ _ = _
  exact (FamilyPoints.multiplyAlong_congr G _ _ _ _ hbase hleft hright).trans
    (FamilyPoints.fiberInclusion_mul S G s u v).symm

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {σ : A →ₐ[ℂ] R}

/-- The actual tensor-family formula identifies multiplication in any
fiber chart obtained by slicing the total chart, wherever the product
remains in that chart. -/
theorem familyMultiplicationCoordinates_eq_fiber_chart
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A))
    (hf : ∀ z ∈ N.charts.pairDomain, ∀ a d,
      f z (a ⊗ₜ[R] d) = N.charts.total.symm (z.1, z.2.1) a *
        N.charts.total.symm (z.1, z.2.2) d)
    (q : F) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) E)
    (hs : c.source =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)) ⁻¹'
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source)
    (ht : c.target = {v | (q, v) ∈ N.charts.total.target})
    (hc : ∀ z ∈ c.source, c z =
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) z)).2)
    (hinv : ∀ v ∈ c.target,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (c.symm v) =
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).symm (q, v))
    (u v : E) (hpair : (q, (u, v)) ∈ N.charts.pairDomain)
    (hproduct : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
        (LocalizedFamily.Abelian.RelativeCharts.affineFamilyMultiplication G b i hi) (f (q, (u, v))) ∈
          (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source) :
    (LocalizedFamily.Abelian.RelativeCharts.familyMultiplicationCoordinates G b i hi N f (q, (u, v))).2 =
      c (c.symm u * c.symm v) := by
  have hu : u ∈ c.target := ht ▸ hpair.1
  have hv : v ∈ c.target := ht ▸ hpair.2
  have hleft : (f (q, (u, v))).comp Algebra.TensorProduct.includeLeft =
      N.charts.total.symm (q, u) := by
    ext a
    change f (q, (u, v)) (a ⊗ₜ[R] (1 : A)) = _
    rw [hf _ hpair, map_one, mul_one]
  have hright : (f (q, (u, v))).comp
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ) =
        N.charts.total.symm (q, v) := by
    ext a
    change f (q, (u, v)) ((1 : A) ⊗ₜ[R] a) = _
    rw [hf _ hpair, map_one, one_mul]
  have hmul := affineFamilyMultiplication_fiber_points G b i hi s (c.symm u) (c.symm v)
    (f (q, (u, v)))
    (by rw [hleft, hinv u hu]; rfl)
    (by rw [hright, hinv v hv]; rfl)
  have hsource : c.symm u * c.symm v ∈ c.source := by
    rw [hs]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)
      (c.symm u * c.symm v) ∈ (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source
    rw [← hmul]
    exact hproduct
  change (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
      (LocalizedFamily.Abelian.RelativeCharts.affineFamilyMultiplication G b i hi) (f (q, (u, v))))).2 = _
  rw [hmul, hc _ hsource]

end Abelian.RelativeCharts

end ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws

end

end OAI
