import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints
import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies
import OAI.ArithmeticGeometry.Descent.CMVariety.RelativeProductMaps

/-! # Localized Family -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.Descent.CMVariety.LocalizedFamily

/-!
Actual abelian-scheme multiplication on the relative pair families. The
map is built from the given abelian scheme's group law, and its analytic
coordinate dependence follows from the actual scheme-map theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff TensorProduct _root_.CategoryTheory.MonObj

namespace Abelian.FamilyPoints

variable {S T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}

/-- Regard a map with specified base projection as an actual point of
the abelian scheme over that test scheme. -/
def asRelativePoint (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (l : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A) (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) :
    A.Points (Over.mk q.left) :=
  Over.homMk l.left (congrArg Over.Hom.left hl)

/-- Multiply two actual maps lying over the same base using the genuine
group law of the abelian scheme. -/
def multiplyAlong (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (l r : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A)
    (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) (hr : r ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A := by
  let k := asRelativePoint A q l hl * asRelativePoint A q r hr
  exact Over.homMk k.left (by
    change k.left ≫ (A.scheme.hom ≫ S.hom) = T.hom
    rw [← Category.assoc, k.w]
    exact q.w)

theorem multiplyAlong_projection (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (l r : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A)
    (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) (hr : r ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) :
    multiplyAlong A q l r hl hr ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q := by
  apply Over.OverMorphism.ext
  exact (asRelativePoint A q l hl * asRelativePoint A q r hr).w

theorem asRelativePoint_identity (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (h : (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) :
    asRelativePoint A q (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) h = 1 := by
  let t : Over.mk q.left ⟶ Over.mk (𝟙 S.left) :=
    Over.homMk q.left (Category.comp_id _)
  have he : asRelativePoint A q (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) h =
      t ≫ (1 : Over.mk (𝟙 S.left) ⟶ A.scheme) := by
    apply Over.OverMorphism.ext
    rfl
  rw [he, MonObj.comp_one]

theorem multiplyAlong_identity_left (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (r : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A)
    (hl : (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q)
    (hr : r ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) :
    multiplyAlong A q (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) r hl hr = r := by
  apply Over.OverMorphism.ext
  change (asRelativePoint A q (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) hl *
    asRelativePoint A q r hr).left = r.left
  rw [asRelativePoint_identity, one_mul]
  rfl

theorem multiplyAlong_identity_right (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (l : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A) (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q)
    (hr : (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) :
    multiplyAlong A q l (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) hl hr = l := by
  apply Over.OverMorphism.ext
  change (asRelativePoint A q l hl *
    asRelativePoint A q (q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) hr).left = l.left
  rw [asRelativePoint_identity, mul_one]
  rfl

theorem multiplyAlong_eq_right_of_left_identity
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (l r : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A)
    (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) (hr : r ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q)
    (h : l = q ≫ AbelianFamilyPoints.FamilyPoints.identitySection S A) : multiplyAlong A q l r hl hr = r := by
  subst l
  exact multiplyAlong_identity_left A q r hl hr

/-- The actual relative multiplication commutes with every change of
test scheme, in particular with evaluation at a native complex point. -/
theorem multiplyAlong_comp {U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (q : T ⟶ S)
    (l r : T ⟶ AbelianFamilyPoints.FamilyPoints.total S A)
    (hl : l ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) (hr : r ≫ AbelianFamilyPoints.FamilyPoints.projection S A = q) (k : U ⟶ T) :
    k ≫ multiplyAlong A q l r hl hr =
      multiplyAlong A (k ≫ q) (k ≫ l) (k ≫ r)
        (by rw [Category.assoc, hl]) (by rw [Category.assoc, hr]) := by
  let kt : Over.mk (k ≫ q).left ⟶ Over.mk q.left := Over.homMk k.left rfl
  have hm := MonObj.comp_mul kt (asRelativePoint A q l hl) (asRelativePoint A q r hr)
  apply Over.OverMorphism.ext
  exact congrArg (fun u : Over.mk (k ≫ q).left ⟶ A.scheme => u.left) hm

end Abelian.FamilyPoints

namespace Abelian.RelativeCharts

theorem affineSpec_comp {R A B : Type}
    [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (f : R →ₐ[ℂ] A) (h : A →ₐ[ℂ] B) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B h ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A f =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R B (h.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom h.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

def tensorLeft : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[R] A) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[R] A) Algebra.TensorProduct.includeLeft

def tensorRight : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[R] A) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[R] A)
    ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ)

theorem tensorInclusions_same_base :
    tensorLeft (R := R) (A := A) ≫
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) =
      tensorRight (R := R) (A := A) ≫
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[R] A) _ ≫ _ =
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[R] A) _ ≫ _
  rw [affineSpec_comp, affineSpec_comp]
  apply congrArg (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (A ⊗[R] A))
  ext r
  change algebraMap R A r ⊗ₜ[R] (1 : A) = (1 : A) ⊗ₜ[R] algebraMap R A r
  simpa only [Algebra.smul_def, mul_one] using
    (TensorProduct.smul_tmul (R := R) r (1 : A) (1 : A))

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}

/-- Apply the actual family group law to the two inclusions from the
relative affine tensor product. -/
def affineFamilyMultiplication
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G)
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[R] A) ⟶ AbelianFamilyPoints.FamilyPoints.total S G := by
  let l := tensorLeft (R := R) (A := A) ≫ i
  let r := tensorRight (R := R) (A := A) ≫ i
  have hsame : r ≫ AbelianFamilyPoints.FamilyPoints.projection S G = l ≫ AbelianFamilyPoints.FamilyPoints.projection S G := by
    dsimp only [r, l]
    rw [Category.assoc, Category.assoc, hi, ← Category.assoc, ← Category.assoc,
      tensorInclusions_same_base]
  exact FamilyPoints.multiplyAlong G (l ≫ AbelianFamilyPoints.FamilyPoints.projection S G) l r rfl hsame

/-- At an actual identity point, the constructed relative multiplication
is the identity point. This compares the tensor-character construction
with the abelian scheme's given unit and multiplication. -/
theorem affineFamilyMultiplication_identity
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G)
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x ≫
        AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
      (affineFamilyMultiplication G b i hi) (RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x := by
  let k := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (A ⊗[R] A) (RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl)
  have hleft : k ≫ (tensorLeft (R := R) (A := A) ≫ i) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x := by
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[R] A) Algebra.TensorProduct.includeLeft ≫ i)
      (RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl) = _
    refine (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap (CommAlgCat.of ℂ A)
      (CommAlgCat.of ℂ (A ⊗[R] A)) Algebra.TensorProduct.includeLeft i
      (RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl)).trans ?_
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i
      ((RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl).comp Algebra.TensorProduct.includeLeft) = _
    rw [RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint_left]
  have hright : k ≫ (tensorRight (R := R) (A := A) ≫ i) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x := by
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[R] A)
        ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ) ≫ i)
      (RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl) = _
    refine (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap (CommAlgCat.of ℂ A)
      (CommAlgCat.of ℂ (A ⊗[R] A))
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ) i
      (RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl)).trans ?_
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i
      ((RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl).comp
        ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℂ)) = _
    rw [RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint_right]
  unfold affineFamilyMultiplication
  change k ≫ FamilyPoints.multiplyAlong _ _ _ _ _ _ = _
  rw [FamilyPoints.multiplyAlong_comp]
  refine (FamilyPoints.multiplyAlong_eq_right_of_left_identity _ _ _ _ _ _ ?_).trans hright
  rw [← Category.assoc k (tensorLeft (R := R) (A := A) ≫ i)
    (AbelianFamilyPoints.FamilyPoints.projection S G), hleft]
  exact hx

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {s : A →ₐ[ℂ] R}

/-- In the constructed normalized relative charts, the actual abelian
scheme's multiplication is analytic on the open set where both inputs
and the product belong to the chosen chart. -/
theorem exists_analytic_affineFamilyMultiplication
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s) :
    ∃ f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A),
      (∀ z ∈ N.charts.pairDomain, ∀ a c,
        f z (a ⊗ₜ[R] c) = N.charts.total.symm (z.1, z.2.1) a *
          N.charts.total.symm (z.1, z.2.2) c) ∧
      ContDiffOn ℂ ω
        (fun z => AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
            (affineFamilyMultiplication G b i hi) (f z)))
        (N.charts.pairDomain ∩ {z |
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
            (affineFamilyMultiplication G b i hi) (f z) ∈
              (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source}) := by
  obtain ⟨f, hp, hf⟩ := N.charts.exists_pairPointFamily
  exact ⟨f, hp, AnalyticSchemeFamilies.Abelian.RelativeCharts.contDiffOn_schemeImage_in_affineChart
    (CommAlgCat.of ℂ (A ⊗[R] A)) (CommAlgCat.of ℂ A)
    (affineFamilyMultiplication G b i hi) i N.charts.total N.forwardTotal
    f N.charts.pairDomain N.charts.pairDomain_isOpen hf⟩

/-- The actual family multiplication written in the constructed coordinates. -/
def familyMultiplicationCoordinates
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s)
    (f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A)) : F × (E × E) → F × E :=
  fun z => AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
      (affineFamilyMultiplication G b i hi) (f z))

/-- Around an actual identity point, the multiplication coordinate domain
is a constructed open neighborhood, and the central product has zero
fiber coordinate. The multiplication is the given abelian scheme law. -/
theorem exists_local_analytic_familyMultiplication
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s)
    (hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x ≫
        AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) :
    ∃ (f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A)) (U : Set (F × (E × E))),
      (∀ z ∈ N.charts.pairDomain, ∀ a c,
        f z (a ⊗ₜ[R] c) = N.charts.total.symm (z.1, z.2.1) a *
          N.charts.total.symm (z.1, z.2.2) c) ∧
      IsOpen U ∧
      (N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), (0, 0)) ∈ U ∧
      U ⊆ N.charts.pairDomain ∧
      ContDiffOn ℂ ω (familyMultiplicationCoordinates G b i hi N f) U ∧
      familyMultiplicationCoordinates G b i hi N f
          (N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), (0, 0)) =
        (N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), 0) ∧
      ∀ z ∈ U,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A))
          (affineFamilyMultiplication G b i hi) (f z) ∈
            (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source := by
  obtain ⟨f, hp, hf⟩ := N.charts.exists_pairPointFamily
  let z₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  let m := affineFamilyMultiplication G b i hi
  let c := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
  let p := fun z => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A)) m (f z)
  let U := N.charts.pairDomain ∩ p ⁻¹' c.source
  have hU : IsOpen U := AnalyticSchemeFamilies.Abelian.RelativeCharts.isOpen_schemeImage_affineChart_domain
    (CommAlgCat.of ℂ (A ⊗[R] A)) (CommAlgCat.of ℂ A) m i N.charts.total
    f N.charts.pairDomain N.charts.pairDomain_isOpen hf
  have hp₀ : p (z₀, (0, 0)) = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x := by
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[R] A)) m
      (f (z₀, (0, 0))) = _
    rw [N.pairPointFamily_center f hp]
    exact affineFamilyMultiplication_identity G b i hi x hx
  have hzU : (z₀, (0, 0)) ∈ U := by
    refine ⟨N.section_mem_pairDomain _ N.center, ?_⟩
    change p (z₀, (0, 0)) ∈ c.source
    rw [hp₀]
    exact ⟨x, N.charts.point, rfl⟩
  refine ⟨f, U, hp, hU, hzU, inter_subset_left, ?_, ?_, fun _ hz => hz.2⟩
  · exact AnalyticSchemeFamilies.Abelian.RelativeCharts.contDiffOn_schemeImage_in_affineChart
      (CommAlgCat.of ℂ (A ⊗[R] A)) (CommAlgCat.of ℂ A) m i N.charts.total N.forwardTotal
      f N.charts.pairDomain N.charts.pairDomain_isOpen hf
  · change c (p (z₀, (0, 0))) = (z₀, 0)
    rw [hp₀]
    exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans N.center_coordinates

end Abelian.RelativeCharts

end ArithmeticGeometry.Descent.CMVariety.LocalizedFamily

namespace ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts
section

/-!
Construct the algebra map of the actual abelian identity section after a
principal localization of the affine base. Its retraction identity is
proved from the genuine group section and the commuting affine diagram.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}

/-- Whenever the actual identity point lies in the chosen affine total
open, a principal base neighborhood has an actual algebraic section map.
It restricts to the canonical localization map on the base algebra. -/
theorem exists_identitySection_localization
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (xBase : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)
    (hBase : (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b xBase ≫
      AbelianFamilyPoints.FamilyPoints.identitySection S G) ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i)) :
    ∃ a : R, xBase a ≠ 0 ∧ ∃ σ : A →ₐ[ℂ] Localization.Away a,
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a) σ ≫ i =
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away a)
          (Algebra.algHom ℂ R (Localization.Away a)) ≫ b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G ∧
      σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a) ∧
      ∀ (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (hy : y a ≠ 0),
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i
            ((AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a hy).comp σ) =
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y ≫
            AbelianFamilyPoints.FamilyPoints.identitySection S G := by
  have hBase' : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R)
      (b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) xBase ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i) := by
    simpa only [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map] using hBase
  obtain ⟨a, ha, σ, hfac, hpoint⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition
    (CommAlgCat.of ℂ R) (CommAlgCat.of ℂ A) (b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) i xBase hBase'
  have hcomp : (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a) σ ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A)) ≫ b =
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away a)
          (Algebra.algHom ℂ R (Localization.Away a)) ≫ b := by
    calc
      _ = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a) σ ≫ i) ≫
          AbelianFamilyPoints.FamilyPoints.projection S G := by
        rw [Category.assoc, Category.assoc, hi]
      _ = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away a)
          (Algebra.algHom ℂ R (Localization.Away a)) ≫
            (b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G)) ≫ AbelianFamilyPoints.FamilyPoints.projection S G :=
        congrArg (fun f => f ≫ AbelianFamilyPoints.FamilyPoints.projection S G) hfac
      _ = _ := by
        simp only [Category.assoc, AbelianFamilyPoints.FamilyPoints.identitySection_projection, Category.comp_id]
  have heq : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a) σ ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) =
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away a)
          (Algebra.algHom ℂ R (Localization.Away a)) := by
    apply Over.OverMorphism.ext
    apply (cancel_mono b.left).mp
    exact congrArg (fun t : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ S => t.left) hcomp
  have hσ : σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a) := by
    apply (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away a)).injective
    rw [← affineSpec_comp]
    exact heq
  refine ⟨a, ha, σ, hfac, hσ, ?_⟩
  intro y hy
  exact (hpoint ⟨y, hy⟩).trans
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp (CommAlgCat.of ℂ R) b
      (AbelianFamilyPoints.FamilyPoints.identitySection S G) y)

end

section

/-!
Localize both the base and total affine algebra of an actual section.
The induced section of the localized total algebra is constructed from
the localization universal property, and the retraction identity is proved.
-/

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

def localizedBaseMap (a : R) :
    Localization.Away a →ₐ[ℂ] Localization.Away (algebraMap R A a) :=
  Localization.awayMapₐ (IsScalarTower.toAlgHom ℂ R A) a

theorem localizedBaseMap_algebraMap (a r : R) :
    localizedBaseMap (A := A) a (algebraMap R (Localization.Away a) r) =
      algebraMap A (Localization.Away (algebraMap R A a)) (algebraMap R A r) := by
  change IsLocalization.Away.map (Localization.Away a) (Localization.Away (algebraMap R A a))
    (algebraMap R A) a (algebraMap R (Localization.Away a) r) = _
  simp only [IsLocalization.Away.map, IsLocalization.map_eq]

theorem localizedBaseMap_smooth [Algebra.Smooth R A] (a : R) :
    (localizedBaseMap (A := A) a).toRingHom.Smooth := by
  exact RingHom.Smooth.isStableUnderBaseChange.localizationPreserves.away
    (algebraMap R A) a (Localization.Away a) (Localization.Away (algebraMap R A a))
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The section extends because the inverted total element maps to the
inverted base element, which is an actual unit. -/
def localizedSection (a : R) (σ : A →ₐ[ℂ] Localization.Away a)
    (hσ : σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a)) :
    Localization.Away (algebraMap R A a) →ₐ[ℂ] Localization.Away a := by
  have hu : IsUnit (σ (algebraMap R A a)) := by
    have h := DFunLike.congr_fun hσ a
    change σ (algebraMap R A a) = algebraMap R (Localization.Away a) a at h
    rw [h]
    exact IsLocalization.Away.algebraMap_isUnit a
  exact IsLocalization.Away.liftAlgHom (algebraMap R A a) hu

theorem localizedSection_algebraMap (a : R) (σ : A →ₐ[ℂ] Localization.Away a)
    (hσ : σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a))
    (t : A) :
    localizedSection a σ hσ (algebraMap A (Localization.Away (algebraMap R A a)) t) = σ t := by
  simp only [localizedSection, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The actual localized section is a retraction of the localized base map. -/
theorem localizedSection_retraction (a : R) (σ : A →ₐ[ℂ] Localization.Away a)
    (hσ : σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a)) :
    (localizedSection a σ hσ).comp (localizedBaseMap (A := A) a) =
      AlgHom.id ℂ (Localization.Away a) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext r
  change localizedSection a σ hσ
    (localizedBaseMap (A := A) a (algebraMap R (Localization.Away a) r)) =
      algebraMap R (Localization.Away a) r
  rw [localizedBaseMap_algebraMap, localizedSection_algebraMap]
  exact DFunLike.congr_fun hσ r

end

/-!
The simultaneous base and total-space localizations preserve the actual
scheme projection and identity-section diagrams. These are equalities of
scheme morphisms, derived from the localization algebra maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

def affineAwayMap (a : R) : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away a) (Algebra.algHom ℂ R (Localization.Away a))

instance affineAwayMap_isOpenImmersion (a : R) : IsOpenImmersion (affineAwayMap a).left := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a))))
  infer_instance

omit [Algebra R A] [IsScalarTower ℂ R A] in
theorem affineAwayMap_point (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (a : R) (ha : y a ≠ 0) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Localization.Away a))
      (affineAwayMap a ≫ b) (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a ha) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y := by
  have h := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap (CommAlgCat.of ℂ R)
    (CommAlgCat.of ℂ (Localization.Away a)) (Algebra.algHom ℂ R (Localization.Away a)) b
    (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a ha)
  exact h.trans (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b)
    (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp y a ha))

theorem localized_affine_projection
    (p : X ⟶ S) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (a : R) :
    (affineAwayMap (algebraMap R A a) ≫ i) ≫ p =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (Localization.Away a) (Localization.Away (algebraMap R A a))
        (localizedBaseMap (A := A) a) ≫ (affineAwayMap a ≫ b) := by
  have he : affineAwayMap (algebraMap R A a) ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) =
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (Localization.Away a) (Localization.Away (algebraMap R A a))
          (localizedBaseMap (A := A) a) ≫ affineAwayMap a := by
    unfold affineAwayMap
    rw [affineSpec_comp, affineSpec_comp]
    apply congrArg (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (Localization.Away (algebraMap R A a)))
    ext r
    exact (localizedBaseMap_algebraMap (A := A) a r).symm
  rw [Category.assoc, hi, ← Category.assoc, he, Category.assoc]

theorem localized_affine_section
    (sectionMap : S ⟶ X) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (a : R) (σ : A →ₐ[ℂ] Localization.Away a)
    (hσ : σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a))
    (hfac : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a) σ ≫ i =
      affineAwayMap a ≫ b ≫ sectionMap) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (Localization.Away (algebraMap R A a)) (Localization.Away a)
        (localizedSection a σ hσ) ≫ (affineAwayMap (algebraMap R A a) ≫ i) =
      (affineAwayMap a ≫ b) ≫ sectionMap := by
  have he : (localizedSection a σ hσ).comp
      (Algebra.algHom ℂ A (Localization.Away (algebraMap R A a))) = σ := by
    ext t
    exact localizedSection_algebraMap a σ hσ t
  rw [← Category.assoc]
  unfold affineAwayMap
  rw [affineSpec_comp, he]
  exact hfac.trans (Category.assoc _ _ _).symm

end ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts

end

end OAI
