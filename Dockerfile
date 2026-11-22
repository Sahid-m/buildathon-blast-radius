# Blast Radius entry. Same base image the organisers labelled with.
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90

ENV PYTHONDONTWRITEBYTECODE=1 PIP_NO_CACHE_DIR=1 PIP_DISABLE_PIP_VERSION_CHECK=1

# Same packages as the labelling environment (pinned).
COPY requirements.lock /app/requirements.lock
RUN pip install -r /app/requirements.lock

# sqlglot at the pinned commit (GitHub archive of that exact commit).
ARG SQLGLOT_SHA=eb11aec4be8cb2122afe713a4816662c3f0fb2fa
RUN python -c "import urllib.request,tarfile,io,os; \
data=urllib.request.urlopen('https://github.com/tobymao/sqlglot/archive/${SQLGLOT_SHA}.tar.gz').read(); \
tarfile.open(fileobj=io.BytesIO(data)).extractall('/opt', filter='tar'); \
os.rename('/opt/sqlglot-${SQLGLOT_SHA}', '/opt/sqlglot')" \
 && python -m compileall -q /opt/sqlglot/sqlglot /opt/sqlglot/tests || true

COPY selector.py covmap.json /app/
RUN python -m compileall -q /app && chmod -R a+rX /opt/sqlglot /app

CMD ["python", "/app/selector.py"]
