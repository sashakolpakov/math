import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Split Frame Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport

noncomputable section

/-! Split action frames transfer through actual PEL isomorphisms and
through the proved Tate comparison for field extensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {R : Type u} [CommRing R] {g N s q : ℕ} [Fact q.Prime]
  {S : Scheme.{u}} {F G : PEL.PELFamilyData R g N S} (T : Over S)
  (χ : Fin s × Bool → R →+* ℤ_[q])

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.rationalTateEquiv (a : PELModuli.PELFamilyIso F G) :
    Rational.rationalTateModule F.abelian.scheme T q ≃ₗ[ℚ_[q]] Rational.rationalTateModule G.abelian.scheme T q :=
  LinearEquiv.ofLinearMap (Rational.rationalTateMap a.abelian.hom) (Rational.rationalTateMap a.abelian.inv)
    (by simp only [← Functor.rationalTateMap_comp, Iso.inv_hom_id, Functor.rationalTateMap_id])
    (by simp only [← Functor.rationalTateMap_comp, Iso.hom_inv_id, Functor.rationalTateMap_id])

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.rationalTateEquiv_action (a : PELModuli.PELFamilyIso F G) (r : R)
    (z : Rational.rationalTateModule F.abelian.scheme T q) :
    a.rationalTateEquiv T (Rational.rationalTateMap (T := T) (q := q)
        (End.endSchemeMap F.abelian.scheme (F.action r)) z) =
      Rational.rationalTateMap (T := T) (q := q) (End.endSchemeMap G.abelian.scheme (G.action r))
        (a.rationalTateEquiv T z) := by
  have h : Rational.rationalTateMap (T := T) (q := q)
      (End.endSchemeMap F.abelian.scheme (F.action r) ≫ a.abelian.hom) =
    Rational.rationalTateMap (T := T) (q := q)
      (a.abelian.hom ≫ End.endSchemeMap G.abelian.scheme (G.action r)) := by
    congr 1
    exact a.equivariant r
  simp only [Functor.rationalTateMap_comp] at h
  exact LinearMap.congr_fun h z

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.transportFrame (a : PELModuli.PELFamilyIso F G)
    (e : Rational.SplitTateFrame s G.abelian.scheme T q) : Rational.SplitTateFrame s F.abelian.scheme T q :=
  (a.rationalTateEquiv T).trans e

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.transportFrame_equivariant (a : PELModuli.PELFamilyIso F G)
    (e : Rational.SplitTateFrame s G.abelian.scheme T q) (he : Rational.IsSplitActionFrame G T q χ e) :
    Rational.IsSplitActionFrame F T q χ (a.transportFrame T e) := by
  intro r z v i
  change e (a.rationalTateEquiv T (Rational.rationalTateMap (T := T) (q := q)
    (End.endSchemeMap F.abelian.scheme (F.action r)) z)) v i = _
  rw [a.rationalTateEquiv_action]
  exact he r (a.rationalTateEquiv T z) v i

variable {K k R₀ : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field k] [CommRing R₀]
  (b : Spec (.of k) ⟶ Spec (.of K))
  (P : PEL.PELFamilyData R₀ g N (Spec (.of K)))
  (χ₀ : Fin s × Bool → R₀ →+* ℤ_[q])

theorem fieldBaseChangeRationalTateEquiv_action (r : R₀)
    (z : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q) :
    FieldBaseChange.fieldBaseChangeRationalTateEquiv b q P.abelian
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of K)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action r)) z) =
      Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
        (End.endSchemeMap (P.pullback b).abelian.scheme ((P.pullback b).action r))
          (FieldBaseChange.fieldBaseChangeRationalTateEquiv b q P.abelian z) := by
  simpa only [P.pullback_action_schemeMap] using
    FieldBaseChange.fieldBaseChangeRationalTateEquiv_natural b q P.abelian
      (End.endSchemeMap P.abelian.scheme (P.action r)) z

def descendFieldFrame
    (e : Rational.SplitTateFrame s (P.pullback b).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q :=
  (FieldBaseChange.fieldBaseChangeRationalTateEquiv b q P.abelian).trans e

theorem descendFieldFrame_equivariant
    (e : Rational.SplitTateFrame s (P.pullback b).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (he : Rational.IsSplitActionFrame (P.pullback b) (Over.mk (𝟙 (Spec (.of k)))) q χ₀ e) :
    Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of K)))) q χ₀ (descendFieldFrame b P e) := by
  intro r z v i
  change e (FieldBaseChange.fieldBaseChangeRationalTateEquiv b q P.abelian
    (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of K)))) (q := q)
      (End.endSchemeMap P.abelian.scheme (P.action r)) z)) v i = _
  rw [fieldBaseChangeRationalTateEquiv_action]
  exact he r _ v i

omit [CharZero K] [IsAlgClosed K] in
private def extendFrame_with_comparison
    (c : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule (P.pullback b).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (hc : ∀ r z, c (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of K)))) (q := q)
        (End.endSchemeMap P.abelian.scheme (P.action r)) z) =
      Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
        (End.endSchemeMap (P.pullback b).abelian.scheme ((P.pullback b).action r)) (c z))
    (e : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q)
    (he : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of K)))) q χ₀ e) :
    {e' : Rational.SplitTateFrame s (P.pullback b).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q //
      Rational.IsSplitActionFrame (P.pullback b) (Over.mk (𝟙 (Spec (.of k)))) q χ₀ e'} := by
  refine ⟨c.symm.trans e, ?_⟩
  intro r z v i
  let f := Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of K)))) (q := q)
    (End.endSchemeMap P.abelian.scheme (P.action r))
  let g := Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
    (End.endSchemeMap (P.pullback b).abelian.scheme ((P.pullback b).action r))
  have hn : ∀ w, c (f w) = g (c w) := hc r
  have hinv : c.symm (g z) = f (c.symm z) := by
    calc
      c.symm (g z) = c.symm (g (c (c.symm z))) :=
        congrArg (fun w => c.symm (g w)) (c.apply_symm_apply z).symm
      _ = c.symm (c (f (c.symm z))) := congrArg (fun w => c.symm w) (hn (c.symm z)).symm
      _ = f (c.symm z) := c.symm_apply_apply _
  change e (c.symm (g z)) v i = _ * e (c.symm z) v i
  rw [hinv]
  exact he r (c.symm z) v i

private def extendedFieldFrameData
    (e : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q)
    (he : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of K)))) q χ₀ e) :
    {e' : Rational.SplitTateFrame s (P.pullback b).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q //
      Rational.IsSplitActionFrame (P.pullback b) (Over.mk (𝟙 (Spec (.of k)))) q χ₀ e'} :=
  extendFrame_with_comparison (q := q) (s := s) b P χ₀
    (FieldBaseChange.fieldBaseChangeRationalTateEquiv b q P.abelian)
    (fieldBaseChangeRationalTateEquiv_action (q := q) b P) e he

def extendFieldFrame
    (e : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q)
    (he : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of K)))) q χ₀ e) :
    Rational.SplitTateFrame s (P.pullback b).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  (extendedFieldFrameData b P χ₀ e he).val

theorem extendFieldFrame_equivariant
    (e : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of K)))) q)
    (he : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of K)))) q χ₀ e) :
    Rational.IsSplitActionFrame (P.pullback b) (Over.mk (𝟙 (Spec (.of k)))) q χ₀
      (extendFieldFrame b P χ₀ e he) :=
  (extendedFieldFrameData b P χ₀ e he).property

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport
