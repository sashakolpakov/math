import OAI.NumberTheory.PadicHodge.GeometricComparison.WeaklyEtale
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback

/-! # Pro Etale Fst -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleFst.ProEtaleFrobeniusSite

noncomputable section

/-! The actual pro-étale base-change functor of absolute Frobenius is naturally isomorphic to the identity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction

universe u
variable (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0)

def component (U : X.ProEt) :
    U ≅ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).obj U :=
  MorphismProperty.Over.isoMk
    (WeaklyEtale.WeaklyEtaleFrobenius.absoluteFrobenius_square p hp hX U.hom).isoPullback
    (WeaklyEtale.WeaklyEtaleFrobenius.absoluteFrobenius_square p hp hX U.hom).isoPullback_hom_snd

theorem component_fst (U : X.ProEt) :
    (component p hp X hX U).hom.left ≫ pullback.fst U.hom (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) =
      AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp U.left (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hX U.hom) :=
  (WeaklyEtale.WeaklyEtaleFrobenius.absoluteFrobenius_square p hp hX U.hom).isoPullback_hom_fst

theorem component_snd (U : X.ProEt) :
    (component p hp X hX U).hom.left ≫ pullback.snd U.hom (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) = U.hom :=
  (component p hp X hX U).hom.w

private theorem naturality_of_projections {U V S : Scheme.{u}}
    (a : U ⟶ S) (b : V ⟶ S) (F : S ⟶ S) (s : U ⟶ U) (t : V ⟶ V) (f : U ⟶ V)
    (u : U ⟶ pullback a F) (v : V ⟶ pullback b F)
    (m : pullback a F ⟶ pullback b F)
    (hu : u ≫ pullback.fst a F = s) (hv : v ≫ pullback.fst b F = t)
    (hu' : u ≫ pullback.snd a F = a) (hv' : v ≫ pullback.snd b F = b)
    (hm : m ≫ pullback.fst b F = pullback.fst a F ≫ f)
    (hm' : m ≫ pullback.snd b F = pullback.snd a F)
    (hs : f ≫ t = s ≫ f) (hf : f ≫ b = a) : f ≫ v = u ≫ m := by
  apply pullback.hom_ext
  · rw [Category.assoc, hv, Category.assoc, hm, ← Category.assoc, hu]
    exact hs
  · rw [Category.assoc, hv', Category.assoc, hm', hu']
    exact hf

def baseChangeIso : 𝟭 X.ProEt ≅ AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) :=
  NatIso.ofComponents (component p hp X hX) (fun {U V} f => by
    apply MorphismProperty.Over.Hom.ext
    change f.left ≫ (component p hp X hX V).hom.left =
      (component p hp X hX U).hom.left ≫
        ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).map f).left
    exact naturality_of_projections U.hom V.hom (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)
      _ _ f.left _ _ _ (component_fst p hp X hX U) (component_fst p hp X hX V)
      (component_snd p hp X hX U) (component_snd p hp X hX V)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ f.left).symm f.w)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleFst.ProEtaleFrobeniusSite
