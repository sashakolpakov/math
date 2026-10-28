import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover

/-! # Hom Zariski Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomZariskiSheaf

noncomputable section

/-! Module maps after base change form a sheaf for the big Zariski topology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

theorem moduleHom_isSeparatedFor_zariski (T : Over X) (S : Sieve T)
    (hS : S ∈ (Scheme.zariskiTopology.over X) T) :
    Presieve.IsSeparatedFor (HomPresheaf.moduleHomPresheaf M N) S.arrows := by
  intro s φ ψ hφ hψ
  apply HomOpenCover.moduleHom_openCover_injective M N T
    (fun i : Relative.ZariskiOpenCover.relativeZariskiOpenIndex T S => i.val) (Relative.ZariskiOpenCover.relativeZariskiOpenIndex_covers T S hS)
  intro i
  exact (hφ _ i.property).trans (hψ _ i.property).symm

theorem moduleHom_isSheafFor_zariski (T : Over X) (S : Sieve T)
    (hS : S ∈ (Scheme.zariskiTopology.over X) T) :
    Presieve.IsSheafFor (HomPresheaf.moduleHomPresheaf M N) S.arrows := by
  let U : Relative.ZariskiOpenCover.relativeZariskiOpenIndex T S → T.left.Opens := fun i => i.val
  have hU := Relative.ZariskiOpenCover.relativeZariskiOpenIndex_covers T S hS
  apply Presieve.isSheafFor_subsieve_aux (HomPresheaf.moduleHomPresheaf M N) (Relative.ZariskiOpenCover.relativeZariskiOpenCover_le T S)
  · exact (Presieve.isSheafFor_iff_generate _).mp (HomOpenCover.moduleHom_isSheafFor_openCover M N T U hU)
  · intro Y f _
    exact moduleHom_isSeparatedFor_zariski M N Y _
      ((Scheme.zariskiTopology.over X).pullback_stable f (Relative.ZariskiOpenCover.relativeOpenCoverSieve_mem T U hU))

theorem moduleHomPresheaf_isSheaf_zariski :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over X) (HomPresheaf.moduleHomPresheaf M N) :=
  (isSheaf_iff_isSheaf_of_type _ _).mpr (moduleHom_isSheafFor_zariski M N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomZariskiSheaf
