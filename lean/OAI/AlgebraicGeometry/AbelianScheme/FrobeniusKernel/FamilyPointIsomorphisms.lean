import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PullIsoLaws

/-! # Family Point Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction

noncomputable section

/-! Evaluate actual family isomorphisms along a point of the abelian
factor, with their native pullback and composition laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom Pseudofunctor.LocallyDiscreteOpToCat

theorem familyProjection_parameter_eq {S : Scheme.{u}} {V W B T : Over S}
    (q : V ⟶ W) (x y : T ⟶ V ⊗ B) (h : x ≫ (q ▷ B) = y ≫ (q ▷ B)) :
    (x ≫ fst V B) ≫ q = (y ≫ fst V B) ≫ q := by
  have hh := congrArg (fun m => m ≫ fst W B) h
  simpa only [Category.assoc, whiskerRight_fst] using hh

theorem familyProjection_fiber_eq {S : Scheme.{u}} {V W B T : Over S}
    (q : V ⟶ W) (x y : T ⟶ V ⊗ B) (h : x ≫ (q ▷ B) = y ≫ (q ▷ B)) :
    x ≫ snd V B = y ≫ snd V B := by
  have hh := congrArg (fun m => m ≫ snd W B) h
  simpa only [Category.assoc, whiskerRight_snd] using hh

def familyPointGraph {S : Scheme.{u}} {V B T : Over S} (x : T ⟶ V ⊗ B) : T ⟶ T ⊗ B :=
  lift (𝟙 T) (x ≫ snd V B)

theorem familyPointGraph_factor {S : Scheme.{u}} {V B T : Over S}
    (x y : T ⟶ V ⊗ B) (h : x ≫ snd V B = y ≫ snd V B) :
    familyPointGraph x ≫ ((y ≫ fst V B) ▷ B) = y := by
  apply hom_ext
  · simp only [familyPointGraph, Category.assoc, whiskerRight_fst, lift_fst_assoc, Category.id_comp]
  · simpa only [familyPointGraph, Category.assoc, whiskerRight_snd, lift_snd] using h

theorem familyPointGraph_naturality {S : Scheme.{u}} {V B T U : Over S}
    (t : U ⟶ T) (x : T ⟶ V ⊗ B) (x' : U ⟶ V ⊗ B) (hx : t ≫ x = x') :
    familyPointGraph x' ≫ (t ▷ B) = t ≫ familyPointGraph x := by
  apply hom_ext
  · simp only [familyPointGraph, Category.assoc, whiskerRight_fst,
      lift_fst_assoc, Category.id_comp, lift_fst, Category.comp_id]
  · have h := congrArg (fun m => m ≫ snd V B) hx
    simpa only [familyPointGraph, Category.assoc, whiskerRight_snd, lift_snd] using h.symm

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {V T U : Over S}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (V ⊗ A.scheme).left) (x y : T ⟶ V ⊗ A.scheme)
variable (hxy : x ≫ snd V A.scheme = y ≫ snd V A.scheme)
variable (e : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((x ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf ≅
  (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((y ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf)

def familyPointIso : Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L) x ≅
    Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L) y :=
  Picard.PoincareBundle.PullbackFiberComposition.pullIso (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) (A := V ⊗ A.scheme) (B := V ⊗ A.scheme)
    (M := L.sheaf) (N := L.sheaf)
    (x := (x ≫ fst V A.scheme) ▷ A.scheme) (y := (y ≫ fst V A.scheme) ▷ A.scheme)
    e (familyPointGraph x) x y (familyPointGraph_factor x x rfl) (familyPointGraph_factor x y hxy)

abbrev familyPointIso_natural (t : U ⟶ T) (x' y' : U ⟶ V ⊗ A.scheme)
    (hx : t ≫ x = x') (hy : t ≫ y = y')
    (hxy' : x' ≫ snd V A.scheme = y' ≫ snd V A.scheme)
    (e' : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((x' ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((y' ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf) :=
  PullIsoLaws.Construction.pullIso_square_of_eq (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (A := V ⊗ A.scheme) (B := V ⊗ A.scheme) (L := L.sheaf) (M := L.sheaf)
    (x := (x ≫ fst V A.scheme) ▷ A.scheme) (y := (y ≫ fst V A.scheme) ▷ A.scheme) e
    (familyPointGraph x) x y (t ▷ A.scheme)
    ((x' ≫ fst V A.scheme) ▷ A.scheme) ((y' ≫ fst V A.scheme) ▷ A.scheme)
    t (familyPointGraph x') x' y' (familyPointGraph_factor x x rfl) (familyPointGraph_factor x y hxy)
    (FamilyNormalizedPullback.Construction.familyMap_comp A t (x ≫ fst V A.scheme) (x' ≫ fst V A.scheme)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ fst V A.scheme) hx)))
    (FamilyNormalizedPullback.Construction.familyMap_comp A t (y ≫ fst V A.scheme) (y' ≫ fst V A.scheme)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ fst V A.scheme) hy)))
    hx hy (familyPointGraph_factor x' x' rfl) (familyPointGraph_factor x' y' hxy')
    (familyPointGraph_naturality t x x' hx).symm e'

abbrev familyPointIso_comp (z : T ⟶ V ⊗ A.scheme)
    (hyz : y ≫ snd V A.scheme = z ≫ snd V A.scheme)
    (e' : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((y ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((z ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf) :=
  PullIsoLaws.Construction.pullIso_trans_of_base_eq (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (A := V ⊗ A.scheme) (B := V ⊗ A.scheme) (D := V ⊗ A.scheme)
    (L := L.sheaf) (M := L.sheaf) (N := L.sheaf)
    (x := (x ≫ fst V A.scheme) ▷ A.scheme) (y := (y ≫ fst V A.scheme) ▷ A.scheme)
    (z := (z ≫ fst V A.scheme) ▷ A.scheme) e e' (familyPointGraph x) (familyPointGraph y)
    (congrArg (fun v => lift (𝟙 T) v) hxy.symm) x y z
    (familyPointGraph_factor x x rfl) (familyPointGraph_factor x y hxy)
    (familyPointGraph_factor x z (hxy.trans hyz))
    (familyPointGraph_factor y y rfl) (familyPointGraph_factor y z hyz)

theorem familyPointIso_comp_of_eq (z : T ⟶ V ⊗ A.scheme)
    (hyz : y ≫ snd V A.scheme = z ≫ snd V A.scheme)
    (e' : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((y ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((z ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf)
    (e'' : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((x ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((z ≫ fst V A.scheme) ▷ A.scheme).left L).sheaf)
    (he : e ≪≫ e' = e'') :
    familyPointIso A L x y hxy e ≪≫ familyPointIso A L y z hyz e' =
      familyPointIso A L x z (hxy.trans hyz) e'' :=
  (familyPointIso_comp A L x y hxy e z hyz e').trans
    (congrArg (familyPointIso A L x z (hxy.trans hyz)) he)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction
