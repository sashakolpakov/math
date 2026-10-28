import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PullbackComposition

/-! # Forgetful Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-!
Natural forgetful maps from embedded polarized classes to the original
moduli presheaf and to the concrete presheaf of flat closed families.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P : Over S} {g N : ℕ} {δ : Fin g → ℕ} {T U : Over S}

theorem PolarizedIsomorphisms.EmbeddedPolarizedClasses.closedFamily_pullback (f : T ⟶ U)
    (q : PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N U) :
    (q.pullback f).closedFamily = (FamilyFunctor.embeddedFlatFamilyFunctor P).map f.op q.closedFamily := by
  induction q using Quotient.inductionOn with
  | h A => exact A.closedFamily_pullback f

theorem PolarizedIsomorphisms.EmbeddedPolarizedClasses.forget_pullback (f : T ⟶ U)
    (q : PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N U) :
    (q.pullback f).forget = Moduli.Isomorphisms.PolarizedLevelClasses.pullback f.left q.forget := by
  induction q using Quotient.inductionOn with
  | h A => rfl

/-- Forget the projective embedding while retaining the complete polarized full-level class. -/
def ForgetfulMaps.embeddedForgetModuli (P : Over S) (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) :
    PullbackComposition.embeddedPolarizedFunctor P g δ N ⟶ Moduli.Functor.polarizedLevelModuliOver g δ N S where
  app T := TypeCat.ofHom PolarizedIsomorphisms.EmbeddedPolarizedClasses.forget
  naturality _ _ f := by
    ext q
    exact PolarizedIsomorphisms.EmbeddedPolarizedClasses.forget_pullback f.unop q

/-- Forget the algebraic group, polarization, and level, retaining the defining ideal family. -/
def ForgetfulMaps.embeddedForgetClosedFamily (P : Over S) (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) :
    PullbackComposition.embeddedPolarizedFunctor P g δ N ⟶ FamilyFunctor.embeddedFlatFamilyFunctor P ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom (fun q => ULift.up (PolarizedIsomorphisms.EmbeddedPolarizedClasses.closedFamily q))
  naturality _ _ f := by
    ext q
    exact congrArg ULift.up (PolarizedIsomorphisms.EmbeddedPolarizedClasses.closedFamily_pullback f.unop q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
