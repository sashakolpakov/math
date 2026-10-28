import OAI.AlgebraicGeometry.FormalGeometry.Completion.BundleSectionAlgebraNaturality

/-! # Section Algebra -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra

noncomputable section

/-! A single, derived finite-type algebra classifies actual sections on
all affine base changes of a flat projective line-bundle family, naturally
for geometric pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

structure GeometricSectionAlgebraRepresentation {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) where
  algebra : CommAlgCat.{u} Γ(S, ⊤)
  finiteType : Algebra.FiniteType Γ(S, ⊤) algebra
  equivalence : ∀ (Y T : Scheme.{u}) [IsAffine T] (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S)
    (_hp : IsPullback f ρ π g),
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤) ≃
      (algebra →ₐ[Γ(S, ⊤)] Γ(T, ⊤))
  natural : ∀ (Y Z T T' : Scheme.{u}) [IsAffine T] [IsAffine T']
    (f : Y ⟶ X) (j : Z ⟶ Y) (ρ : Y ⟶ T) (τ : Z ⟶ T') (g : T ⟶ S) (t : T' ⟶ T)
    (hp : IsPullback f ρ π g) (_hj : j ≫ ρ = τ ≫ t) (ho : IsPullback (j ≫ f) τ π (t ≫ g))
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤)),
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(T', ⊤) := (t ≫ g).appTop.hom.toAlgebra
    equivalence Z T' (j ≫ f) τ (t ≫ g) ho (GlobalSectionComposition.Construction.globalSectionCompositePullback f j M s) =
      (ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
        (ModelCoordinateComposition.Construction.appTop_comp_ringHom g t)).comp (equivalence Y T f ρ g hp s)

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

include P in
theorem projectiveLineBundle_sectionAlgebraRepresentation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    Nonempty (GeometricSectionAlgebraRepresentation X.hom L.sheaf) := by
  obtain ⟨C, φ, _hq, _hb, hf, hp, ht⟩ :=
    Quotients.FiniteDescent.ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.exists_actual_finite_projective X P L
  have := hf 0
  have := hf 1
  have := hp 0
  have := hp 1
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let U := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P
  have hU := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers X P
  have ha := fun q (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex _ q) =>
    Quotients.FiniteDescent.ProjectiveCechFlat.Construction.ProjectiveCechComplex.intersection_affine X P q i.1
  refine ⟨{
    algebra := CommAlgCat.of Γ(S, ⊤) (Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebra (C := C))
    finiteType := SymmetricAlgebraFiniteType.Construction.finiteProjectiveKernelAlgebra_finiteType Γ(S, ⊤) (C.X 0) (C.d 0 1).hom
    equivalence := fun Y T _ f ρ g h => LineBundleSectionAlgebra.Construction.finiteModelSectionAlgebraEquiv f X.hom ρ g h L.sheaf U hU ha φ ht
    natural := ?_ }⟩
  intro Y Z T T' _ _ f j ρ τ g t h hj ho s
  exact BundleSectionAlgebraNaturality.Construction.finiteModelSectionAlgebraEquiv_natural f j X.hom ρ τ g t h hj ho L.sheaf U hU ha φ ht s

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra
