import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification

/-! # Affine Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.AffineDescent

noncomputable section

/-!
# Descent of geometric line bundles on affine schemes for PoincareBundle

The input is a genuine line bundle with a descent coaction on its global
sections. The two equations are the usual counit and cocycle conditions.
The output is a genuine line bundle on the base, with its pullback
identified with the input line bundle.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- Descent data on the actual global sections of a geometric line bundle. -/
structure LineDatum (f : R ⟶ S) where
  line : Line.Bundles.LineBundle (Spec S)
  coaction : (moduleSpecΓFunctor (R := S)).obj line.sheaf ⟶
    (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj
      ((moduleSpecΓFunctor (R := S)).obj line.sheaf)
  counit : coaction ≫ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.ε.app
      ((moduleSpecΓFunctor (R := S)).obj line.sheaf) = 𝟙 _
  coassoc : coaction ≫ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.δ.app
      ((moduleSpecΓFunctor (R := S)).obj line.sheaf) =
    coaction ≫ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.map coaction

/-- The module descent datum extracted from a geometric line datum. -/
def LineDatum.moduleDatum {f : R ⟶ S} (D : LineDatum f) :
    Affine.Descent.ModuleDatum f.hom where
  A := (moduleSpecΓFunctor (R := S)).obj D.line.sheaf
  a := D.coaction
  counit := D.counit
  coassoc := D.coassoc

/-- The underlying module is invertible because the input is locally a
rank-one geometric line bundle. -/
theorem LineDatum.moduleDatum_invertible {f : R ⟶ S} (D : LineDatum f) :
    Module.Invertible S D.moduleDatum.A :=
  Affine.Classification.globalSections_invertible D.line

/-- Effective descent of a geometric line bundle over a noetherian affine base. -/
def descend [IsNoetherianRing R] (f : R ⟶ S) (hf : f.hom.FaithfullyFlat)
    (D : LineDatum f) : Line.Bundles.LineBundle (Spec R) := by
  have := D.moduleDatum_invertible
  exact TildePullback.descendedLineBundle f hf D.moduleDatum

/-- Pullback of the descended geometric bundle is the original bundle. -/
def descendPullbackIso [IsNoetherianRing R] (f : R ⟶ S) (hf : f.hom.FaithfullyFlat)
    (D : LineDatum f) :
    (Scheme.Modules.pullback (Spec.map f)).obj (descend f hf D).sheaf ≅ D.line.sheaf := by
  have := D.moduleDatum_invertible
  exact TildePullback.descendedLineBundlePullbackIso f hf D.moduleDatum ≪≫
    QuasiCoherent.affineTildeIso D.line

/-- A competing descended bundle with the same module descent data is
isomorphic to the constructed geometric bundle. -/
def descendUniqueIso [IsNoetherianRing R] (f : R ⟶ S) (hf : f.hom.FaithfullyFlat)
    (D : LineDatum f) (L : Line.Bundles.LineBundle (Spec R))
    (e : (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj f.hom)).obj
      ((moduleSpecΓFunctor (R := R)).obj L.sheaf) ≅ D.moduleDatum) :
    L.sheaf ≅ (descend f hf D).sheaf :=
  (QuasiCoherent.affineTildeIso L).symm ≪≫ (tilde.functor R).mapIso
    (Affine.Descent.descendedModule_unique f.hom hf D.moduleDatum
      ((moduleSpecΓFunctor (R := R)).obj L.sheaf) e).some

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.AffineDescent
