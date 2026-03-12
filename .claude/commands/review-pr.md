Fetch review comments from the current PR and address all of them.

## Steps

1. **Identify the PR**: Determine the PR number for the current branch:
   ```
   gh pr view --json number,url,title
   ```

2. **Fetch review comments**: Get all review comments (both top-level and inline):
   ```
   gh pr view --json reviews,comments
   gh api repos/{owner}/{repo}/pulls/{number}/comments
   ```
   Parse and list every actionable comment. Ignore resolved comments.

3. **Read the affected files**: Before making any changes, read every file that has review comments so you understand the full context.

4. **Address each comment**: For each review comment:
   - Understand what the reviewer is asking for
   - Apply the change at the commented location
   - **Search the entire codebase for all other places where the same issue applies** and fix those too — do not limit fixes to only the lines the reviewer pointed at
   - Verify compilation with `lake env lean <file>` for each modified file

5. **Commit and push**:
   ```
   git add <files>
   git commit -m "address review comments"
   LEAN4_GUARDRAILS_BYPASS=1 git push
   ```

6. **Update CLAUDE.md**: If any review comment reveals a style rule, naming convention, or coding pattern that should be followed going forward, add it to the appropriate section of CLAUDE.md so it is not repeated in future PRs.

7. **Report back**: List each comment and what was done to address it.

## Important
- Address ALL comments, not just some.
- Apply fixes globally, not just at the specific line the reviewer commented on.
- If a comment is unclear, state your interpretation and proceed with the most reasonable fix.
- Do not leave any comment unaddressed.
