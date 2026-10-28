import Mathlib

/-! # Terminal Module Projective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalModuleProjective

noncomputable section

/-! Constant free module sheaves are projective at a terminal object whose covering sieves are maximal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R]
  [HasSheafify J (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
variable {T : C} (hT : ∀ S : Sieve T, S ∈ J T → S = ⊤)

include hT in
theorem epi_surjective {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op T)) := by
  have : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{w} R) f).mpr inferInstance
  intro x
  have h := hT _ (Presheaf.imageSieve_mem J f.hom x)
  have hx := Sieve.id_mem_iff_eq_top.mpr h
  simpa [Presheaf.imageSieve] using hx

include hT in
theorem projective (hterminal : IsTerminal T) :
    Projective ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)) := by
  have : ((sheafSections J (ModuleCat.{w} R)).obj (op T)).PreservesEpimorphisms :=
    ⟨fun f _ => ConcreteCategory.epi_of_surjective _ (epi_surjective J R hT f)⟩
  exact (constantSheafAdj J (ModuleCat.{w} R) hterminal).map_projective _ inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalModuleProjective
