import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.SourceFamilyAcyclicity

/-! # Presentation Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationAcyclicity

noncomputable section

/-! A free presentation sheaf is acyclic whenever its actual free representable sources are acyclic. -/

open _root_.CategoryTheory

universe u v z

variable {C : Type (max u v)} [Category.{v} C] {ι : Type v} (F : ι → C)
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{max u v} R)]
  [HasExt.{z} (Sheaf J (ModuleCat.{max u v} R))]

theorem subsingleton {H : Sheaf J (ModuleCat.{max u v} R)} (I : InjectiveResolution H) (n : ℕ)
    [∀ i, Subsingleton (Abelian.Ext.{z} (Sheaf.freeYoneda J (F i) (ModuleCat.of R R)) H (n + 1))] :
    Subsingleton (Abelian.Ext.{z} (PresentationSheafSections.sheaf F R J) H (n + 1)) :=
  SourceFamilyAcyclicity.Family.subsingleton (fun i => Sheaf.freeYoneda J (F i) (ModuleCat.of R R)) I
    (fun q => PresentationSheafSections.familyEquiv F R J (I.cocomplex.X q))
    (fun q a i => PresentationSheafSections.familyEquiv_natural F R J
      (I.cocomplex.d q (q + 1)) a i) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationAcyclicity
