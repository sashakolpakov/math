import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-! # Total Biadditive Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalBiadditiveExt

noncomputable section

/-! The finite summands determine additive and biadditive maps out of
the actual total, even when the target has a larger universe. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' w
variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

theorem sum_components (n : ℕ) (x : (K.total (.up ℕ)).X n) :
    (∑ i : Fin (n+1), K.ιTotal (.up ℕ) i (n-i) n (by change (i : ℕ)+(n-i)=n; omega)
      ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (n-i) n x)) = x := by
  have h := ConcreteCategory.congr_hom (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_decomposition K n) x
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

theorem additive_ext {Z : Type w} [AddCommGroup Z] (n : ℕ)
    {f g : (K.total (.up ℕ)).X n →+ Z}
    (h : ∀ p q (hpq : p+q=n) (x : (K.X p).X q),
      f (K.ιTotal (.up ℕ) p q n hpq x) = g (K.ιTotal (.up ℕ) p q n hpq x)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  rw [← sum_components K n x, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => h i (n-i) (by omega) _)

variable {S : Type u'} [CommRing S]
  (L : HomologicalComplex₂ (ModuleCat.{v'} S) (.up ℕ) (.up ℕ)) [L.HasTotal (.up ℕ)]

theorem biadditive_ext {Z : Type w} [AddCommGroup Z] (n m : ℕ)
    {f g : (K.total (.up ℕ)).X n →+ (L.total (.up ℕ)).X m →+ Z}
    (h : ∀ p a q b (hpa : p+a=n) (hqb : q+b=m)
      (x : (K.X p).X a) (y : (L.X q).X b),
      f (K.ιTotal (.up ℕ) p a n hpa x) (L.ιTotal (.up ℕ) q b m hqb y) =
        g (K.ιTotal (.up ℕ) p a n hpa x) (L.ιTotal (.up ℕ) q b m hqb y)) : f = g := by
  apply additive_ext K n
  intro p a hpa x
  exact additive_ext L m (fun q b hqb y => h p a q b hpa hqb x y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalBiadditiveExt
