import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions

/-! # Supported Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCoordinates

noncomputable section

/-! Original nested-pushforward supported cohomology has the literal
source-open additive coordinates, preserving restriction and the action
of the original function on the affine source neighborhood. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem action_square {D : Type*} [Category D] {A B C E : D}
    (a : A ⟶ C) (b : B ⟶ E) (e : C ≅ E)
    (r : A ⟶ B) (s : A ⟶ A) (t : B ⟶ B) (v : E ⟶ E)
    (hu : r ≫ b = a ≫ e.hom) (hm : s ≫ r = r ≫ t) (hs : t ≫ b = b ≫ v) :
    s ≫ a = a ≫ e.hom ≫ v ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hu, ← Category.assoc s r, hm, Category.assoc, hs, ← Category.assoc r b, hu]
  exact Category.assoc _ _ _

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) {ι : Type} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (N : Y.Modules) (c q : ℕ)

private abbrev forgetScalars : ModuleCat.{0} Γ(Z,U) ⥤ AddCommGrpCat := forget₂ _ _
private abbrev original := OpenFixedClass.source f i U hU N
private abbrev cohomology := OpenRestriction.supportedFunctor U W c q
private abbrev source (V : Y.Opens) := OpenFixedClass.source f i U hU (OpenRestriction.extension V N)

def wideIso : (forgetScalars U).obj ((cohomology U W c q).obj (original f i U hU N)) ≅
    (AffinePrincipal.Injective.Comparison.source (OpenReindex.wideOpens (f ≫ i) U hU) W N c).homology q :=
  Supported.SingleCoefficientCoordinates.iso W Γ(Z,U) (OpenReindex.wideOpens (f ≫ i) U hU) N
    (original f i U hU N) (OpenScalar.diagramIso f i U hU N) c q

def localIso (V : Y.Opens) :
    (forgetScalars U).obj ((cohomology U W c q).obj (source f i U hU N V)) ≅
      (AffinePrincipal.Injective.Comparison.source (OpenReindex.geometricOpens (f ≫ i) U hU V) W N c).homology q :=
  Supported.SingleCoefficientCoordinates.iso W Γ(Z,U) (OpenReindex.geometricOpens (f ≫ i) U hU V) N
    (source f i U hU N V) (OpenScalar.localDiagramIso f i U hU N V) c q

theorem restriction_square (V : Y.Opens) :
    (forgetScalars U).map (OpenRestriction.supportedMap f i U hU V N W c q) ≫ (localIso f i U hU W N c q V).hom =
      (wideIso f i U hU W N c q).hom ≫
        homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap
          (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU V)
          (OpenReindex.geometricInclusion (f ≫ i) U hU V) W N c) q :=
  Supported.SingleCoefficientCoordinates.restriction_natural W Γ(Z,U)
    (OpenReindex.wideOpens (f ≫ i) U hU) N (original f i U hU N)
    (OpenScalar.diagramIso f i U hU N)
    (OpenReindex.geometricOpens (f ≫ i) U hU V) (OpenReindex.geometricInclusion (f ≫ i) U hU V)
    (OpenScalar.localDiagramIso f i U hU N V) (OpenRestriction.map f i U hU V N)
    (OpenScalar.restriction_square f i U hU N V) c q

def coefficientMap {P : Y.Modules} (a : N ⟶ P) : original f i U hU N ⟶ original f i U hU P :=
  Principal.SectionPresheaf.moduleHom U hU ((Scheme.Modules.pushforward i).map ((Scheme.Modules.pushforward f).map a))

theorem wide_natural {P : Y.Modules} (a : N ⟶ P) :
    (forgetScalars U).map ((cohomology U W c q).map (coefficientMap f i U hU N a)) ≫
        (wideIso f i U hU W P c q).hom =
      (wideIso f i U hU W N c q).hom ≫
        homologyMap (AffinePrincipal.Injective.Comparison.sourceMap (OpenReindex.wideOpens (f ≫ i) U hU) W N c a) q :=
  Supported.SingleCoefficientCoordinates.coefficient_natural W Γ(Z,U)
    (OpenReindex.wideOpens (f ≫ i) U hU) N (original f i U hU N)
    (OpenScalar.diagramIso f i U hU N)
    (OpenScalar.diagramIso f i U hU P) (coefficientMap f i U hU N a) a
    (OpenScalar.diagramIso_natural f i U hU a) c q

theorem scalar_square (z : Γ(Y,(f ≫ i) ⁻¹ᵁ U)) :
    (forgetScalars U).map ((cohomology U W c q).map
        (OpenFixedClass.scalar f i U hU N z)) ≫ (wideIso f i U hU W N c q).hom =
      (wideIso f i U hU W N c q).hom ≫
        Principal.SupportedOpenScalar.action (OpenReindex.wideOpens (f ≫ i) U hU) ((f ≫ i) ⁻¹ᵁ U)
          (SupportConditions.wide_bounded (f ≫ i) U hU) W N c z q := by
  let V₀ := (f ≫ i) ⁻¹ᵁ U
  let e := Principal.SupportedOpenScalar.unitIso (OpenReindex.wideOpens (f ≫ i) U hU) V₀
    (SupportConditions.wide_bounded (f ≫ i) U hU) W N c q
  have hu := wide_natural f i U hU W N c q (Open.SubschemeCoefficientUnit.unit V₀ N)
  have hs := wide_natural f i U hU W (OpenRestriction.extension V₀ N) c q
    (Open.SubschemeCoefficientUnit.scalar V₀ N z)
  have hm := congrArg (fun a => (forgetScalars U).map ((cohomology U W c q).map a))
    (OpenScalar.scalar_unit f i U hU N z)
  simp only [CategoryTheory.Functor.map_comp] at hm
  exact action_square (wideIso f i U hU W N c q).hom
    (wideIso f i U hU W (OpenRestriction.extension V₀ N) c q).hom e _ _ _ _ hu hm hs

theorem scalar_fixed_iff (z : Γ(Y,(f ≫ i) ⁻¹ᵁ U))
    (x : (cohomology U W c q).obj (original f i U hU N)) :
    Principal.SupportedOpenScalar.action (OpenReindex.wideOpens (f ≫ i) U hU) ((f ≫ i) ⁻¹ᵁ U)
        (SupportConditions.wide_bounded (f ≫ i) U hU) W N c z q
          ((wideIso f i U hU W N c q).hom x) = (wideIso f i U hU W N c q).hom x ↔
      (cohomology U W c q).map (OpenFixedClass.scalar f i U hU N z) x = x := by
  have h := ConcreteCategory.congr_hom (scalar_square f i U hU W N c q z) x
  simp only [ConcreteCategory.comp_apply] at h
  rw [← h]
  exact (ConcreteCategory.bijective_of_isIso (wideIso f i U hU W N c q).hom).injective.eq_iff

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCoordinates
