import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.SelectContract.Spec

/-! SELECT serialization assurance, separate from static validity and from
independent target-language semantics. Existing unchecked render APIs remain
available for compatibility; they do not carry this certificate. -/
namespace SQLean.RenderContract

/-- Identity-mode reconstruction preserves any independent SELECT derivation,
including its exact ordered output schema and catalog/parameter indices. This
is a theorem about the reconstructed AST, not PostgreSQL execution. -/
theorem identity_validity_preserved
    (certificate : Certificate .identityV01 query)
    (valid : SelectContract.SelectValid validityProfile catalog parameters query output)
    (reconstructed : Advanced.Query)
    (parsed : Advanced.parseQuery certificate.sql = .ok reconstructed) :
    SelectContract.SelectValid validityProfile catalog parameters reconstructed output := by
  have equality : query = reconstructed := by
    have h := certificate.roundTrip
    change Advanced.parseQuery certificate.sql = .ok query at h
    rw [h] at parsed
    exact Except.ok.inj parsed
  rw [← equality]
  exact valid

/-- Parameter translation preserves the independent basic SELECT output schema
for either numbered target. This is still a theorem about the reconstructed AST,
not an assertion that SQLite and PostgreSQL have identical execution semantics. -/
theorem translated_validity_preserved
    (certificate : Certificate renderingProfile query)
    (translated : renderingProfile.translate = true)
    (valid : SelectContract.SelectValid validityProfile catalog parameters query output)
    (reconstructed : Advanced.Query)
    (parsed : parseRendered renderingProfile certificate.sql = .ok reconstructed) :
    SelectContract.SelectValid validityProfile catalog parameters reconstructed output := by
  have h := certificate.roundTrip
  simp only [expectedQuery, translated, ↓reduceIte] at h
  rw [h] at parsed
  have equality := Except.ok.inj parsed
  rw [← equality]
  exact translateParameters_valid valid

end SQLean.RenderContract
