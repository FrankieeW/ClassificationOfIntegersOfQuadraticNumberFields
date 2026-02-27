"""Tasks for building the blueprint."""
from invoke import task


@task
def web(c):
    """Build blueprint website."""
    c.run("cd blueprint && leanblueprint web")


@task
def serve(c, port=8080):
    """Serve generated blueprint site."""
    c.run(f"cd blueprint/web && python -m http.server {port}")
