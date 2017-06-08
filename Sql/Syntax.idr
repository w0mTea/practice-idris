data SqlStatement = AlterTableStmt
                  | AnalyzeStmt
                  | AttachStmt
                  | BeginStmt
                  | CommitStmt
                  | CreateIndexStmt
                  | CreateTableStmt
                  | CreateTriggerStmt
                  | CreateViewStmt
                  | CreateVirtualTableStmt
                  | DeleteStmt
                  | DeleteStmtLimited
                  | DetachStmt
                  | DropIndexStmt
                  | DropTableStmt
                  | DropTriggerStmt
                  | DropViewStmt
                  | InsertStmt
                  | PragmaStmt
                  | ReindexStmt
                  | ReleaseStmt
                  | RollbackStmt
                  | SavepointStmt
                  | SelectStmt
                  | UpdateStmt
                  | UpdateStmtLimited
                  | VacuumStmt

data ExplainStatement = NoExplain Statement
                      | Explain SqlStatement
                      | ExplainQueryPlan SqlStatement

SqlStatements : Type
SqlStatements = List ExplainStatement
