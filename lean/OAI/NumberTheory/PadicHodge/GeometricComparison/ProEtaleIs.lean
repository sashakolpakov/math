import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Pro Etale Is -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleIs.ProEtaleTerminalGeometry

noncomputable section

/-! The actual terminal object of the pro-étale site has the geometry of the base scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (X : Scheme.{u})

def identityIsTerminal : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f => MorphismProperty.Over.Hom.ext
      ((Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f)))

def terminalIso : (⊤_ X.ProEt).left ≅ X :=
  (Scheme.ProEt.forget X ⋙ Over.forget X).mapIso
    (terminalIsTerminal.uniqueUpToIso (identityIsTerminal X))

instance terminal_compact [CompactSpace X] : CompactSpace (⊤_ X.ProEt).left :=
  QuasiCompact.compactSpace_of_compactSpace (terminalIso X).hom

instance terminal_quasiSeparated [QuasiSeparatedSpace X] : QuasiSeparatedSpace (⊤_ X.ProEt).left :=
  quasiSeparatedSpace_of_quasiSeparated (terminalIso X).hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleIs.ProEtaleTerminalGeometry
