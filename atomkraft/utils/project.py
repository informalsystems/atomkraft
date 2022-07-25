import os
import git


def project_root():
    cwd = os.getcwd()
    try:
        git_repo = git.Repo(cwd, search_parent_directories=True)
        return git_repo.git.rev_parse("--show-toplevel")
    except git.InvalidGitRepositoryError:
        return None
