import OAI.ArithmeticGeometry.Descent.CMVariety.ComposedSmoothCharts

/-! # Smooth Relative Neighborhoods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothRelativeNeighborhoods.Abelian.RelativeCharts

noncomputable section

/-!
Construct standard-smooth relative neighborhoods from actual smoothness.
The relative coefficient ring need not be a field: the complex point
supplies a prime ideal where the smooth algebra admits a standard-smooth
principal neighborhood.
-/

open scoped Classical ContDiff

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

omit [Algebra ℂ R] [IsScalarTower ℂ R A] in
/-- Smoothness itself produces the relative finite polynomial chart near
each actual complex point; a relative presentation is not an extra input. -/
theorem exists_relative_submersive_neighborhood [Algebra.Smooth R A]
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ (g : A) (_hg : x g ≠ 0) (n m : ℕ),
      Nonempty (Algebra.SubmersivePresentation R (Localization.Away g) (Fin n) (Fin m)) := by
  let : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  obtain ⟨g, hg, hstd⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R (RingHom.ker x)
  have hxg : x g ≠ 0 := by simpa only [RingHom.mem_ker] using hg
  let : Algebra.IsStandardSmooth R (Localization.Away g) := hstd
  obtain ⟨I, J, hJ, hI, ⟨P⟩⟩ :=
    Algebra.IsStandardSmooth.out (R := R) (S := Localization.Away g)
  let : Finite I := hI
  let : Finite J := hJ
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  exact ⟨g, hxg, Fintype.card I, Fintype.card J,
    ⟨P.reindex (Fintype.equivFin I).symm (Fintype.equivFin J).symm⟩⟩

/-- An actual finite relative presentation on a principal neighborhood
of the specified point. Keeping its finite index types abstract avoids
expanding finite enumerations in analytic norm instances. -/
structure RelativePresentationAt (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) where
  element : A
  nonzero : x element ≠ 0
  VariableIndex : Type
  RelationIndex : Type
  [variablesFintype : Fintype VariableIndex]
  [relationsFintype : Fintype RelationIndex]
  presentation : Algebra.SubmersivePresentation R (Localization.Away element) VariableIndex RelationIndex

attribute [instance] RelativePresentationAt.variablesFintype RelativePresentationAt.relationsFintype

omit [Algebra ℂ R] [IsScalarTower ℂ R A] in
theorem exists_relative_presentationAt [Algebra.Smooth R A] (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Nonempty (RelativePresentationAt (R := R) x) := by
  obtain ⟨g, hg, n, m, ⟨Q⟩⟩ := exists_relative_submersive_neighborhood (R := R) x
  exact ⟨{
    element := g
    nonzero := hg
    VariableIndex := Fin n
    RelationIndex := Fin m
    presentation := Q }⟩

omit [Algebra ℂ R] [Algebra R A] [IsScalarTower ℂ R A] in
theorem localization_chart_inverse_analytic
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : A) (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) E)
    (h : ∀ a : Localization.Away g, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) :
    ∀ a : A, ContDiffOn ℂ ω
      (fun z => (e.lift_openEmbedding
        (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g)).symm z a)
      (e.lift_openEmbedding
        (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g)).target := by
  intro a
  change ContDiffOn ℂ ω
    (fun z => e.symm z (algebraMap A (Localization.Away g) a)) e.target
  exact h (algebraMap A (Localization.Away g) a)

theorem lift_relative_chart_with_eq
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (g : A) (hg : x g ≠ 0)
    (eR : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) F)
    (e₀ : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) E)
    (p : E → F)
    (hxR : (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg).comp
      (IsScalarTower.toAlgHom ℂ R (Localization.Away g)) ∈ eR.source)
    (hx₀ : AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg ∈ e₀.source)
    (hsource : ∀ z ∈ e₀.target,
      (e₀.symm z).comp (IsScalarTower.toAlgHom ℂ R (Localization.Away g)) ∈ eR.source)
    (hproj : ∀ z ∈ e₀.target,
      eR ((e₀.symm z).comp (IsScalarTower.toAlgHom ℂ R (Localization.Away g))) = p z)
    (hinv : ∀ a : Localization.Away g, ContDiffOn ℂ ω (fun z => e₀.symm z a) e₀.target) :
    ∃ eA : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) E,
      x.comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source ∧ x ∈ eA.source ∧
      (∀ z ∈ eA.target,
        (eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source) ∧
      (∀ z ∈ eA.target,
        eR ((eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A)) = p z) ∧
      (∀ a : A, ContDiffOn ℂ ω (fun z => eA.symm z a) eA.target) ∧
      eA = e₀.lift_openEmbedding
        (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g) := by
  let xg := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg
  let inc := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g
  have hi : Topology.IsOpenEmbedding inc :=
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g
  have hbase (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) :
      (inc y).comp (IsScalarTower.toAlgHom ℂ R A) =
        y.comp (IsScalarTower.toAlgHom ℂ R (Localization.Away g)) := by
    ext r
    change y (algebraMap A (Localization.Away g) (algebraMap R A r)) =
      y (algebraMap R (Localization.Away g) r)
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away g)]
  let eA := e₀.lift_openEmbedding hi
  have hinc : inc xg = x := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg
  refine ⟨eA, ?_, ⟨xg, hx₀, hinc⟩, ?_, ?_, ?_, rfl⟩
  · rw [← hinc, hbase]
    exact hxR
  · intro z hz
    change (inc (e₀.symm z)).comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source
    rw [hbase]
    exact hsource z hz
  · intro z hz
    change eR ((inc (e₀.symm z)).comp (IsScalarTower.toAlgHom ℂ R A)) = _
    rw [hbase]
    exact hproj z hz
  · exact localization_chart_inverse_analytic g e₀ hinv

theorem lift_relative_chart
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (g : A) (hg : x g ≠ 0)
    (eR : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) F)
    (e₀ : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) E)
    (p : E → F)
    (hxR : (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg).comp
      (IsScalarTower.toAlgHom ℂ R (Localization.Away g)) ∈ eR.source)
    (hx₀ : AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg ∈ e₀.source)
    (hsource : ∀ z ∈ e₀.target,
      (e₀.symm z).comp (IsScalarTower.toAlgHom ℂ R (Localization.Away g)) ∈ eR.source)
    (hproj : ∀ z ∈ e₀.target,
      eR ((e₀.symm z).comp (IsScalarTower.toAlgHom ℂ R (Localization.Away g))) = p z)
    (hinv : ∀ a : Localization.Away g, ContDiffOn ℂ ω (fun z => e₀.symm z a) e₀.target) :
    ∃ eA : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) E,
      x.comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source ∧ x ∈ eA.source ∧
      (∀ z ∈ eA.target,
        (eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source) ∧
      (∀ z ∈ eA.target,
        eR ((eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A)) = p z) ∧
      ∀ a : A, ContDiffOn ℂ ω (fun z => eA.symm z a) eA.target := by
  obtain ⟨eA, hb, hx, hs, hp, ha, _⟩ :=
    lift_relative_chart_with_eq x g hg eR e₀ p hxR hx₀ hsource hproj hinv
  exact ⟨eA, hb, hx, hs, hp, ha⟩

/-- Concrete compatible local charts, including regular-function
analyticity of their inverse maps. This packages the constructed result. -/
structure CompatibleRelativeCharts
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (p : E → F) where
  base : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) F
  total : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) E
  basePoint : x.comp (IsScalarTower.toAlgHom ℂ R A) ∈ base.source
  point : x ∈ total.source
  mapsTo : ∀ z ∈ total.target,
    (total.symm z).comp (IsScalarTower.toAlgHom ℂ R A) ∈ base.source
  projection : ∀ z ∈ total.target,
    base ((total.symm z).comp (IsScalarTower.toAlgHom ℂ R A)) = p z
  regularTotal : ∀ a : A, ContDiffOn ℂ ω (fun z => total.symm z a) total.target
  regularBase : ∀ r : R, ContDiffOn ℂ ω (fun z => base.symm z r) base.target

theorem nonempty_relativePointCharts
    {I Sigma J Tau : Type} [Fintype I] [Fintype Sigma] [Fintype J] [Fintype Tau]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (g : A)
    (Q : Algebra.SubmersivePresentation R (Localization.Away g) J Tau)
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hg : x g ≠ 0) :
    Nonempty (CompatibleRelativeCharts (R := R) x (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P Q)) := by
  obtain ⟨eR, e₀, hxR, hx₀, hsource, hproj, hinv, hRinv⟩ :=
    ComposedSmoothCharts.Abelian.RelativeCharts.exists_compatible_smooth_charts P Q (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg)
  obtain ⟨eA, hbase, hx, hs, hp, ha⟩ :=
    lift_relative_chart x g hg eR e₀ (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P Q) hxR hx₀ hsource hproj hinv
  exact ⟨⟨eR, eA, hbase, hx, hs, hp, ha, hRinv⟩⟩

/-- A smooth algebra over an explicitly standard-smooth complex base
has actual local charts in which its base map is a coordinate projection.
Both the relative polynomial presentation and the compatible charts are
constructed from smoothness and the point. -/
theorem exists_smooth_relative_point_charts
    {I Sigma : Type} [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    [Algebra.Smooth R A] (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ D : RelativePresentationAt (R := R) x,
      Nonempty (CompatibleRelativeCharts (R := R) x (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P D.presentation)) := by
  obtain ⟨D⟩ := exists_relative_presentationAt (R := R) x
  exact ⟨D, nonempty_relativePointCharts P D.element D.presentation x D.nonzero⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothRelativeNeighborhoods.Abelian.RelativeCharts
