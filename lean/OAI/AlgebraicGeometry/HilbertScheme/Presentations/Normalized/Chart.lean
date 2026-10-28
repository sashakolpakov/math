import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Matrices
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Chart
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus

/-! # Chart -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Chart.Grassmannian

noncomputable section

/-!
Schemes of normalized quotient matrices. They are the closed affine loci
where the chosen columns equal the identity, with a natural representation
over every test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [DecidableEq ι]
variable (a : ι → ν) (S : Scheme.{u})

def normalizedMatrixSubfunctor : Subfunctor (Grassmannian.Chart.matrixFunctor ι ν S) where
  obj _T := {Q | Matrices.Grassmannian.IsNormalized a Q}
  map f _Q hQ := hQ.map f.unop.left.appTop.hom

def normalizationSections (p : ι × ι) : Γ((Grassmannian.Chart.matrixSpace ι ν S).left, ⊤) :=
  AffineSpace.coord S (p.1, a p.2) - (1 : Matrix ι ι Γ(AffineSpace (ι × ν) S, ⊤)) p.1 p.2

theorem normalizationSections_iff {T : Over S} (f : T ⟶ Grassmannian.Chart.matrixSpace ι ν S) :
    (∀ p, f.left.appTop (normalizationSections a S p) = 0) ↔
      Matrices.Grassmannian.IsNormalized a (Grassmannian.Chart.matrixPointEquiv ι ν S T f) := by
  let ψ : Γ(AffineSpace (ι × ν) S, ⊤) →+* Γ(T.left, ⊤) := f.left.appTop.hom
  constructor
  · intro h
    ext i j
    have hp := h (i, j)
    change ψ (AffineSpace.coord S (i, a j) -
      (if i = j then 1 else 0)) = 0 at hp
    change ψ (AffineSpace.coord S (i, a j)) = if i = j then 1 else 0
    by_cases hij : i = j
    · simpa only [ite_eq_left hij, map_sub, map_one, sub_eq_zero] using hp
    · simpa only [ite_eq_right hij, map_sub, map_zero, sub_zero] using hp
  · intro h p
    have hp := congrArg (fun Q : Matrix ι ι Γ(T.left, ⊤) => Q p.1 p.2) h
    change ψ (AffineSpace.coord S (p.1, a p.2) -
      (if p.1 = p.2 then 1 else 0)) = 0
    change ψ (AffineSpace.coord S (p.1, a p.2)) = if p.1 = p.2 then 1 else 0 at hp
    by_cases hij : p.1 = p.2
    · simpa only [ite_eq_left hij, map_sub, map_one, sub_eq_zero] using hp
    · simpa only [ite_eq_right hij, map_sub, map_zero, sub_zero] using hp

def normalizedMatrixPointEquiv (T : Over S) :
    (SectionZeroLocus.sectionZeroSubfunctor (Grassmannian.Chart.matrixSpace ι ν S) (normalizationSections a S)).obj (.op T) ≃
      (normalizedMatrixSubfunctor a S).obj (.op T) where
  toFun f := ⟨Grassmannian.Chart.matrixPointEquiv ι ν S T f.val, (normalizationSections_iff a S f.val).mp f.property⟩
  invFun Q := ⟨(Grassmannian.Chart.matrixPointEquiv ι ν S T).symm Q.val, by
    apply (normalizationSections_iff a S _).mpr
    exact (congrArg (Matrices.Grassmannian.IsNormalized a) ((Grassmannian.Chart.matrixPointEquiv ι ν S T).apply_symm_apply
      (Q.val : Matrix ι ν Γ(T.left, ⊤)))).mpr Q.property⟩
  left_inv f := Subtype.ext ((Grassmannian.Chart.matrixPointEquiv ι ν S T).symm_apply_apply f.val)
  right_inv Q := Subtype.ext ((Grassmannian.Chart.matrixPointEquiv ι ν S T).apply_symm_apply Q.val)

def normalizedMatrixSectionIso :
    (SectionZeroLocus.sectionZeroSubfunctor (Grassmannian.Chart.matrixSpace ι ν S) (normalizationSections a S)).toFunctor ≅
      (normalizedMatrixSubfunctor a S).toFunctor :=
  NatIso.ofComponents (fun T => (normalizedMatrixPointEquiv a S T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro Q
    apply Subtype.ext
    rfl)

theorem normalizedMatrixSectionIso_inclusion :
    (normalizedMatrixSectionIso a S).hom ≫ (normalizedMatrixSubfunctor a S).ι =
      (SectionZeroLocus.sectionZeroSubfunctor (Grassmannian.Chart.matrixSpace ι ν S) (normalizationSections a S)).ι ≫
        (Grassmannian.Chart.matrixRepresentation ι ν S).hom := rfl

/-- A constructed chart and its representation; no representability hypothesis
is used in the construction below. -/
structure NormalizedChartModel where
  chart : Over S
  inclusion : chart ⟶ Grassmannian.Chart.matrixSpace ι ν S
  closed : IsClosedImmersion inclusion.left
  representation : yoneda.obj chart ≅ (normalizedMatrixSubfunctor a S).toFunctor
  compatibility : representation.hom ≫ (normalizedMatrixSubfunctor a S).ι =
    yoneda.map inclusion ≫ (Grassmannian.Chart.matrixRepresentation ι ν S).hom

def normalizedChartModel : NormalizedChartModel a S := by
  apply Classical.choice
  obtain ⟨Z, j, hj, e, he⟩ :=
    SectionZeroLocus.section_zero_locus_representable (Grassmannian.Chart.matrixSpace ι ν S) (normalizationSections a S)
  exact ⟨⟨Z, j, hj, e ≪≫ normalizedMatrixSectionIso a S, by
    rw [Iso.trans_hom, Category.assoc, normalizedMatrixSectionIso_inclusion,
      ← Category.assoc, he]⟩⟩

def normalizedChart : Over S := (normalizedChartModel a S).chart

def normalizedChartInclusion : normalizedChart a S ⟶ Grassmannian.Chart.matrixSpace ι ν S :=
  (normalizedChartModel a S).inclusion

instance normalizedChartInclusion_isClosedImmersion :
    IsClosedImmersion (normalizedChartInclusion a S).left := (normalizedChartModel a S).closed

def normalizedChartRepresentation :
    yoneda.obj (normalizedChart a S) ≅ (normalizedMatrixSubfunctor a S).toFunctor :=
  (normalizedChartModel a S).representation

def universalNormalizedMatrix : Matrix ι ν Γ((normalizedChart a S).left, ⊤) :=
  ((normalizedChartRepresentation a S).hom.app (.op (normalizedChart a S)) (𝟙 _)).val

theorem universalNormalizedMatrix_normalized : Matrices.Grassmannian.IsNormalized a (universalNormalizedMatrix a S) :=
  ((normalizedChartRepresentation a S).hom.app (.op (normalizedChart a S)) (𝟙 _)).property

theorem normalizedChartRepresentation_apply {T : Over S} (f : T ⟶ normalizedChart a S) :
    ((normalizedChartRepresentation a S).hom.app (.op T) f).val =
      (universalNormalizedMatrix a S).map f.left.appTop.hom := by
  have h := congrArg Subtype.val
    (ConcreteCategory.congr_hom ((normalizedChartRepresentation a S).hom.naturality f.op)
      (𝟙 (normalizedChart a S)))
  change ((normalizedChartRepresentation a S).hom.app (.op T) (f ≫ 𝟙 _)).val =
    (universalNormalizedMatrix a S).map f.left.appTop.hom at h
  rwa [Category.comp_id] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Chart.Grassmannian
