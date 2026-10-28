import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaSliceSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Acyclicity

/-! # Yoneda Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaAcyclicity

noncomputable section

/-! Affine slice vanishing implies acyclicity of the original free representable source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' z z'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasCoproducts.{v} A]
  [HasSheafify J A] (U : C) [HasSheafify (J.over U) A] (M : A)
  [HasExt.{z} (Sheaf J A)] [HasExt.{z'} (Sheaf (J.over U) A)]
  [PreservesFiniteLimits (J.overPullback A U)]
  [PreservesFiniteColimits (J.overPullback A U)]
  [(J.overPullback A U).PreservesInjectiveObjects]

instance restriction_additive : (J.overPullback A U).Additive where
  map_add := by intros; rfl

theorem subsingleton {H : Sheaf J A} (I : InjectiveResolution H) (n : ℕ)
    [Subsingleton (Abelian.Ext.{z'} ((constantSheaf (J.over U) A).obj M)
      ((J.overPullback A U).obj H) (n + 1))] :
    Subsingleton (Abelian.Ext.{z} (Sheaf.freeYoneda J U M) H (n + 1)) := by
  let K := ExactInjectiveResolution.map (J.overPullback A U) I
  exact ResolutionHom.Acyclicity.subsingleton I K
    (fun q => YonedaSliceSections.homEquiv J U M (I.cocomplex.X q))
    (fun q a => YonedaSliceSections.homEquiv_natural J U M
      (I.cocomplex.d q (q + 1)) a) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaAcyclicity
