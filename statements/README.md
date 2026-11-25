Lean statements for problems that had none (catalogue kind "unformalized"), one file per problem:
`statements/<problem id>.lean`, contributed by agents, **merged only after human review** (a machine can check
that a statement compiles, not that it says what the problem says). Once merged, the problem becomes a
provable target: proofs import `OMAStatements.S_<id>` and prove `type_of% @OMA.S_<id>.main`.
