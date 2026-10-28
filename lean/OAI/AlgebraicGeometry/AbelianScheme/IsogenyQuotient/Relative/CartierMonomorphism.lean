import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KilledGroupEtale
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleSourceMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierInjection

/-! # Cartier Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierMonomorphism.Construction

noncomputable section

/-! The actual Cartier character-line morphism is a monomorphism over
every base when an invertible integer kills the original kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
  (hkill : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

include hn hkill in
theorem cartierToPicard_mono_of_invertible_kernel_exponent : Mono (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  have : Etale C.dual.X.hom := KilledGroupEtale.Construction.cartierRepresentative_etale_of_killed (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C n hn hkill
  apply EtaleSourceMonomorphism.Construction.etaleSource_mono_of_geometric_injective
  intro k _ _ s
  exact CartierInjection.Construction.cartierToPicard_injective_over_geometric_point f D C s

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierMonomorphism.Construction
